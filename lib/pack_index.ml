(*
 * Copyright (c) 2013-2014 Thomas Gazagnaire <thomas@gazagnaire.org>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *)

open Lwt
open Core_kernel.Std
module Log = Log.Make(struct let section = "pack-index" end)

module T = struct
  type t = {
      offsets       : int SHA1.Map.t;
      crcs          : int32 SHA1.Map.t;
      pack_checksum : SHA1.t;
  } with bin_io, compare, sexp
  let hash (t: t) = Hashtbl.hash t
  include Sexpable.To_stringable (struct type nonrec t = t with sexp end)
  let module_name = "Pack_index"
end
include T
include Identifiable.Make (T)


let empty ?pack_checksum () =
  let pack_checksum = match pack_checksum with
    | None   -> SHA1.of_string "" (* XXX: ugly *)
    | Some c -> c in
  {
   offsets     = SHA1.Map.empty;
   crcs        = SHA1.Map.empty;
   pack_checksum;
  }

let pretty t =
  let buf = Buffer.create 1024 in
  bprintf buf "pack-checksum: %s\n" (SHA1.to_hex t.pack_checksum);
  let l = ref [] in
  SHA1.Map.iter2 ~f:(fun ~key ~data ->
      match data with
      | `Both (offset, crc) -> l := (key, offset, crc) :: !l
      | _ -> assert false
    ) t.offsets t.crcs;
  let l = List.sort ~cmp:(fun (_,o1,_) (_,o2,_) -> Int.compare o1 o2) !l in
  List.iter ~f:(fun (sha1, offset, crc) ->
      bprintf buf "%s: off:%d crc:%ld\n" (SHA1.to_hex sha1) offset crc
    ) l;
  Buffer.contents buf

let id_monad =
  (fun x -> x), (fun x f -> f x)

let lengths { offsets } =
  Log.debug "lengths";
  let rec aux acc = function
    | []    -> List.rev acc
    | [h,_] -> aux ((h, None)::acc) []
    | (h1,l1)::((_,l2)::_ as t) -> aux ((h1, Some (l2-l1))::acc) t in
  let l = SHA1.Map.to_alist offsets in
  let l = List.sort ~cmp:(fun (_,x) (_,y) -> Int.compare x y) l in
  SHA1.Map.of_alist_exn (aux [] l)

let input_header buf =
  let magic = Mstruct.get_string buf 4 in
  if String.(magic <> "\255tOc") then
    Mstruct.parse_error_buf buf "wrong magic index (%S)" magic;
  let version = Mstruct.get_be_uint32 buf in
  if Int32.(version <> 2l) then
    Mstruct.parse_error_buf buf "wrong index version (%ld)" version

let input_keys buf n =
  Log.debug "input: reading the %d object IDs" n;
  let a = Array.create n (SHA1.of_string "") in
  for i=0 to n - 1 do
    a.(i) <- SHA1.input buf;
  done;
  a

let keys buf =
  Log.debug "keys";
  input_header buf;
  Mstruct.shift buf (255 * 4);
  let n = Mstruct.get_be_uint32 buf in
  SHA1.Set.of_array (input_keys buf (Int32.to_int_exn n))

let input buf =
  Log.debug "input";
  input_header buf;
  (* Read the first-level fanout *)
  Log.debug "input: reading the first-level fanout";
  let fanout =
    let a = Array.create 256 0l in
    for i=0 to 255 do
      a.(i) <- Mstruct.get_be_uint32 buf;
    done;
    a 
  in
  let nb_objects = Int32.to_int_exn fanout.(255) in

  (* Read the names *)
  let names = input_keys buf nb_objects in

  (* Read the CRCs *)
  Log.debug "input: reading the %d CRCs" nb_objects;
  let crcs =
    Array.foldi names ~init:SHA1.Map.empty 
      ~f:
      (fun i m name ->
	SHA1.Map.add m ~key:name ~data:(Mstruct.get_be_uint32 buf)
      )
  in
  (* Read the offsets *)
  Log.debug "input: reading the %d offsets" nb_objects;
  let conts = ref [] in
  let offsets =
    Array.foldi names ~init:SHA1.Map.empty
      ~f:
      (fun i m name ->
	let more = match Int.(Mstruct.get_uint8 buf land 128) with
        | 0 -> false
        | _ -> true 
	in
	let n =
          Mstruct.shift buf (-1);
          Mstruct.get_be_uint32 buf 
	in
	if more then begin
	  conts := i :: !conts;
	  m
	end
	else
	  let o = Int32.to_int_exn n in
	  SHA1.Map.add m ~key:name ~data:o
      )
  in
  Log.debug "input: reading the %d large offsets" (List.length !conts);
  let offsets =
    List.fold_left !conts ~init:offsets
      ~f:
      (fun m i ->
	let n = names.(i) in
	let o = Int64.to_int_exn (Mstruct.get_be_uint64 buf) in
	SHA1.Map.add m ~key:n ~data:o
      ) 
  in
  let pack_checksum = SHA1.input buf in
  let _checksum = SHA1.input buf in
  { offsets; crcs; pack_checksum }

let add buf t =
  let n = SHA1.Map.length t.offsets in
  Log.debug "output: %d packed values" n;
  Bigbuffer.add_string buf "\255tOc";
  Misc.add_be_uint32 buf 2l;

  let cmp (k1,_) (k2,_) = SHA1.compare k1 k2 in

  let offsets = List.sort ~cmp (SHA1.Map.to_alist t.offsets) in
  let crcs    = List.sort ~cmp (SHA1.Map.to_alist t.crcs) in

  Log.debug "output: writing the first-level fanout";
  let fanout = Array.create 256 0l in
  List.iter ~f:(fun (key, _) ->
      let str = SHA1.to_string key in
      let n = Char.to_int str.[0] in
      for i = n to 255 do
        fanout.(i) <- Int32.succ fanout.(i)
      done;
    ) offsets;
  Array.iter ~f:(Misc.add_be_uint32 buf) fanout;

  Log.debug "output: writing the %d object IDs" n;
  List.iter ~f:(fun (key, _) ->
      SHA1.add buf key
    ) offsets;

  Log.debug "output: writing the %d CRCs" n;
  List.iter ~f:(fun (_, crc) ->
      Misc.add_be_uint32 buf crc
    ) crcs;

  Log.debug "output: writing the %d offsets" n;
  let conts = ref [] in
  List.iter ~f:(fun (_, offset) ->
      match Int32.of_int offset with
      | Some i -> Misc.add_be_uint32 buf i
      | None   ->
        conts := Int64.of_int_exn offset :: !conts;
        Misc.add_be_uint32 buf 0x80_00_00_00l
    ) offsets;

  Log.debug "output: writing the %d offset continuations" (List.length !conts);
  let str = String.create 8 in
  List.iter ~f:(fun cont ->
      EndianString.BigEndian.set_int64 str 0 cont;
      Bigbuffer.add_string buf str
    ) (List.rev !conts);

  SHA1.add buf t.pack_checksum;

  (* XXX: SHA1.of_bigstring *)
  let str = Bigbuffer.contents buf in
  let checksum = SHA1.create str in
  Bigbuffer.add_string buf (SHA1.to_string checksum)



let int_of_hex hex = Int.of_string ("0x" ^ hex)

class type c_t = object
  method find_offset : SHA1.t -> int option
  method mem         : SHA1.t -> bool
end

class offset_cache size = object (self)
  val keyq = (Queue.create() : SHA1.t Queue.t)
  val tbl = SHA1.Table.create ()

  method add (sha1 : SHA1.t) (offset : int) =
    Log.debug "offset_cache#add: %s -> %d" (SHA1.to_hex sha1) offset;
    Queue.enqueue keyq sha1;
    let _ = SHA1.Table.add tbl ~key:sha1 ~data:offset in
    let qsz = Queue.length keyq in
    if Int.(qsz > size) then begin
      match Queue.dequeue keyq with
      | Some k -> 
          Log.debug "offset_cache#add: qsz=%d shrinking..." qsz;
          SHA1.Table.remove tbl k
      | None -> ()
    end

  method find (sha1 : SHA1.t) =
    Log.debug "offset_cache#find: %s" (SHA1.to_hex sha1);
    SHA1.Table.find tbl sha1

end (* of class Pack_index.offset_cache *)

exception Idx_found of int

class c ?(scan_thresh=8) ?(cache_size=1) (ba : Cstruct.buffer) = object (self)

  val cache = new offset_cache cache_size

  val mutable fanout_ofs  = 0
  val mutable sha1s_ofs   = 0
  val mutable crcs_ofs    = 0
  val mutable offsets_ofs = 0
  val mutable ofs64_ofs   = 0

  val mutable n_sha1s    = 0
  val mutable n_sha1s_4  = 0
  val mutable n_sha1s_20 = 0

  val ofs64_tbl = Int.Table.create ()
  val mutable ofs64_size = None


  method find_offset sha1 =
    Log.debug "c#find_offset: %s" (SHA1.to_hex sha1);

    match cache#find sha1 with
    | Some o -> begin
        Log.debug "c#find_offset: cache hit!";
        Some o
    end
    | None -> begin
        match self#get_sha1_idx sha1 with
        | Some idx -> begin
            let buf = Mstruct.of_bigarray ~off:offsets_ofs ~len:n_sha1s_4 ba in

            Mstruct.shift buf (idx * 4);

            let is64 =
	      match Int.(Mstruct.get_uint8 buf land 128) with
              | 0 -> false
              | _ -> true 
            in
            if is64 then begin
              Log.debug "c#find_offset: 64bit offset";

              let size64 =
                match ofs64_size with
                | Some sz -> sz
                | None -> self#create_ofs64_tbl
              in
              let buf64 = Mstruct.of_bigarray ~off:ofs64_ofs ~len:(size64 * 8) ba in
              match Int.Table.find ofs64_tbl idx with
              | Some idx64 -> begin
                  Mstruct.shift buf64 (idx64 * 8);
                  let o64 = Int64.to_int_exn (Mstruct.get_be_uint64 buf64) in
                  Log.debug "c#find_offset: found:%d" o64;
                  cache#add sha1 o64;
                  Some o64
              end
              | None -> assert false
            end
            else begin
              Mstruct.shift buf (-1);
              let o = Int32.to_int_exn (Mstruct.get_be_uint32 buf) in
              Log.debug "c#find_offset: found:%d" o;
              cache#add sha1 o;
              Some o
            end
        end
        | None -> None
    end

  method mem sha1 =
    Log.debug "c#mem: %s" (SHA1.to_hex sha1);
    match self#find_offset sha1 with
    | Some o -> 
        Log.debug "c#mem: true"; 
        true
    | None -> 
        Log.debug "c#mem: false"; 
        false


  initializer
    let buf = Mstruct.of_bigarray ba in

    input_header buf;

    (* fanout table *)
    fanout_ofs <- Mstruct.offset buf;
    Log.debug "c#<init>: entering fanout table (ofs=%d)" fanout_ofs;
    Mstruct.shift buf (255 * 4);
    n_sha1s <- Int32.to_int_exn (Mstruct.get_be_uint32 buf);
    n_sha1s_4 <- n_sha1s * 4;
    n_sha1s_20 <- n_sha1s * 20;
    Log.debug "c#<init>: n_sha1s:%d" n_sha1s;

    (* sha1 listing *)
    sha1s_ofs <- Mstruct.offset buf;
    Log.debug "c#<init>: entering sha1 listing (ofs=%d)" sha1s_ofs;
    Mstruct.shift buf n_sha1s_20;

    (* crc checksums *)
    crcs_ofs <- Mstruct.offset buf;
    Log.debug "c#<init>: entering crc checksums (ofs=%d)" crcs_ofs;
    Mstruct.shift buf n_sha1s_4;

    (* packfile offsets *)
    offsets_ofs <- Mstruct.offset buf;
    Log.debug "c#<init>: entering packfile offsets (ofs=%d)" offsets_ofs;
    Mstruct.shift buf n_sha1s_4;

    (* large packfile offsets *)
    ofs64_ofs <- Mstruct.offset buf;
    Log.debug "c#<init>: entering large packfile offsets (ofs=%d)" ofs64_ofs;


  method private get_sha1_idx sha1 =
    Log.debug "c#get_sha1_idx: %s" (SHA1.to_hex sha1);
    let fo_idx = self#get_fanout_idx sha1 in
    let buf = Mstruct.of_bigarray ~off:fanout_ofs ~len:(256 * 4) ba in
    let sz0, n =
      if Int.(fo_idx = 0) then begin
	0, Int32.to_int_exn (Mstruct.get_be_uint32 buf)
      end
      else if Int.(fo_idx > 0) then begin
	Mstruct.shift buf ((fo_idx - 1) * 4);
	let sz0 = Int32.to_int_exn (Mstruct.get_be_uint32 buf) in
	let sz1 = Int32.to_int_exn (Mstruct.get_be_uint32 buf) in
	 sz0, sz1 - sz0
      end 
      else
        failwith "Pack_index.c#get_sha1_idx"
    in
    try
      self#scan_sha1s fo_idx sz0 (sha1s_ofs + (sz0 * 20)) n sha1
    with
      Idx_found i -> 
        Log.debug "c#get_sha1_idx: found:%d" i;
        Some i
(*
    match self#scan_sha1s fo_idx sz0 (sha1s_ofs + (sz0 * 20)) n sha1 with
    | Some i ->
        Log.debug "c#get_sha1_idx: found:%d" i;
        Some i
    | None ->
        Log.debug "c#get_sha1_idx: not found";
        None
*)

  method private create_ofs64_tbl =
    Log.debug "c#create_ofs64_tbl";
    let buf = Mstruct.of_bigarray ~off:offsets_ofs ~len:n_sha1s_4 ba in
    let count = ref 0 in
    for i = 0 to n_sha1s - 1 do
      begin
        match Int.(Mstruct.get_uint8 buf land 128) with
        | 0 -> ()
        | _ -> 
            let _ = Int.Table.add ofs64_tbl ~key:i ~data:!count in
            Log.debug "c#create_ofs64_tbl: %d -> %d" i !count;
            incr count
      end;
      Mstruct.shift buf 3
    done;
    ofs64_size <- Some !count;
    !count

  method private get_fanout_idx ?(verbose=true) sha1 =
    let s = SHA1.to_string sha1 in
    let fanout_idx = int_of_char s.[0] in
    fanout_idx

  (* implements binary search *)
  method private scan_sha1s fo_idx idx_ofs ofs n sha1 =
    Log.debug "c#scan_sha1s: fo_idx:%d idx_ofs:%d ofs:%d n:%d" fo_idx idx_ofs ofs n;
    let len = n * 20 in
    let buf = Mstruct.of_bigarray ~off:ofs ~len ba in
(*
    try
*)
      if Int.(n > scan_thresh) then begin
        Log.debug "c#scan_sha1s: %d > scan_thresh(=%d)" n scan_thresh;
        let p = n / 2 in
        Log.debug "c#scan_sha1s: p:%d" p;
        let len' = p * 20 in
        Mstruct.shift buf len';
        let s = SHA1.input buf in
        if SHA1.(s = sha1) then begin
          let idx = idx_ofs + p in
          Log.debug "c#scan_sha1s: idx -> %d" idx;
          raise (Idx_found idx)
        end
        else if self#le_sha1 sha1 s then
          self#scan_sha1s fo_idx idx_ofs ofs p sha1
        else
          let d = p + 1 in
          self#scan_sha1s fo_idx (idx_ofs + d) (ofs + d * 20) (n - p - 1) sha1
      end
      else begin
        Log.debug "c#scan_sha1s: scanning...";
        self#scan_sub idx_ofs sha1 buf 0 (n - 1)
      end
(*
    with
      Idx_found i -> Some i
*)


  method private scan_sub idx_ofs sha1 buf i m =
    if Int.(i > m) then 
      None
    else
      let s = SHA1.input buf in
(*
  assert (Int.(self#get_fanout_idx ~verbose:false s = fo_idx));
 *)
      if SHA1.(s = sha1) then begin
        let idx = idx_ofs + i in
        Log.debug "c#scan_sub: idx -> %d" idx;
        raise (Idx_found idx)
      end
      else
        self#scan_sub idx_ofs sha1 buf (i + 1) m


  method private le_sha1 sha1_0 sha1_1 =
    let s0 = SHA1.to_string sha1_0 in
    let s1 = SHA1.to_string sha1_1 in
(*
    let len = String.length s0 in
    assert (Int.(len = String.length s1));
    let m = len - 1 in
*)
    let rec scan i =
(*
      assert (i <= m);
*)
      let x0 = int_of_char s0.[i] in
      let x1 = int_of_char s1.[i] in
      if Int.(x0 < x1) then
        true
      else if Int.(x0 > x1) then
        false
      else
        scan (i + 1)
    in
    let b = scan 1 in
    Log.debug "c#le_sha1: -> %B" b;
    b


end (* Pack_index.c *)
