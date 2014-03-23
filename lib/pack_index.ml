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
  Log.debugf "lengths";
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
  Log.debugf "input: reading the %d object IDs" n;
  let a = Array.create n (SHA1.of_string "") in
  for i=0 to n - 1 do
    a.(i) <- SHA1.input buf;
  done;
  a

let keys buf =
  Log.debugf "keys";
  input_header buf;
  Mstruct.shift buf (255 * 4);
  let n = Mstruct.get_be_uint32 buf in
  SHA1.Set.of_array (input_keys buf (Int32.to_int_exn n))

let input buf =
  Log.debugf "input";
  input_header buf;
  (* Read the first-level fanout *)
  Log.debugf "input: reading the first-level fanout";
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
  Log.debugf "input: reading the %d CRCs" nb_objects;
  let crcs =
    Array.foldi names ~init:SHA1.Map.empty 
      ~f:
      (fun i m name ->
	SHA1.Map.add m ~key:name ~data:(Mstruct.get_be_uint32 buf)
      )
  in
  (* Read the offsets *)
  Log.debugf "input: reading the %d offsets" nb_objects;
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
  Log.debugf "input: reading the %d large offsets" (List.length !conts);
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
  Log.debugf "output: %d packed values" n;
  Bigbuffer.add_string buf "\255tOc";
  Misc.add_be_uint32 buf 2l;

  let cmp (k1,_) (k2,_) = SHA1.compare k1 k2 in

  let offsets = List.sort ~cmp (SHA1.Map.to_alist t.offsets) in
  let crcs    = List.sort ~cmp (SHA1.Map.to_alist t.crcs) in

  Log.debugf "output: writing the first-level fanout";
  let fanout = Array.create 256 0l in
  List.iter ~f:(fun (key, _) ->
      let str = SHA1.to_string key in
      let n = Char.to_int str.[0] in
      for i = n to 255 do
        fanout.(i) <- Int32.succ fanout.(i)
      done;
    ) offsets;
  Array.iter ~f:(Misc.add_be_uint32 buf) fanout;

  Log.debugf "output: writing the %d object IDs" n;
  List.iter ~f:(fun (key, _) ->
      SHA1.add buf key
    ) offsets;

  Log.debugf "output: writing the %d CRCs" n;
  List.iter ~f:(fun (_, crc) ->
      Misc.add_be_uint32 buf crc
    ) crcs;

  Log.debugf "output: writing the %d offsets" n;
  let conts = ref [] in
  List.iter ~f:(fun (_, offset) ->
      match Int32.of_int offset with
      | Some i -> Misc.add_be_uint32 buf i
      | None   ->
        conts := Int64.of_int_exn offset :: !conts;
        Misc.add_be_uint32 buf 0x80_00_00_00l
    ) offsets;

  Log.debugf "output: writing the %d offset continuations" (List.length !conts);
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



let int_of_hex hex =
  let digit c =
    match c with
    | '0'..'9' -> Char.to_int c - Char.to_int '0'
    | 'A'..'F' -> Char.to_int c - Char.to_int 'A' + 10
    | 'a'..'f' -> Char.to_int c - Char.to_int 'a' + 10
    | c ->
      let msg = Printf.sprintf "int_of_hex: %S is invalid" (String.make 1 c) in
      raise (Invalid_argument msg) 
  in
  let n = String.length hex in
  let result = ref 0 in
  for i = 0 to n - 1 do
    result := !result + (digit hex.[i]) * (Int.of_float (16. ** (float (n - 1 - i))))
  done;
  !result


class type c_t = object
  method find_offset : SHA1.t -> int option
  method mem         : SHA1.t -> bool
end

class c (ba : Cstruct.buffer) = object (self)
  val mutable index = empty ()
  val mutable fanout_index_vec = [|0L;0L;0L;0L|]

  method find_offset sha1 =
    Log.debugf "c#find_offset: %s" (SHA1.to_hex sha1);
    match SHA1.Map.find index.offsets sha1 with
    | Some o -> Some o
    | None -> begin
	self#update_index (self#get_fanout_idx sha1);
	SHA1.Map.find index.offsets sha1
    end

  method mem sha1 =
    Log.debugf "c#mem: %s" (SHA1.to_hex sha1);
    let i = (self#get_fanout_idx sha1) in
    if not (self#is_loaded i) then
      self#update_index i;
    SHA1.Map.mem index.offsets sha1


  method private get_fanout_idx sha1 =
    let hex = SHA1.to_hex sha1 in
    let hd = String.sub hex 0 2 in
    let fanout_idx = int_of_hex hd in
    Log.debugf "c#get_fanout_idx: %s -> %s -> %d" hex hd fanout_idx;
    fanout_idx

  method private is_loaded fanout_idx =
    let i = fanout_idx / 64 in
    let m = fanout_idx mod 64 in
    let x = Int64.shift_left 1L (64 - m) in
    Log.debugf "c#is_loaded: i:%d m:%d x:%Ld" i m x;
    let b = Int64.((bit_and fanout_index_vec.(i) x) = x) in
    Log.debugf "c#is_loaded: %d -> %B" fanout_idx b;
    b

  method private set_loaded fanout_idx =
    Log.debugf "c#set_loaded: %d" fanout_idx;
    let i = fanout_idx / 64 in
    let m = fanout_idx mod 64 in
    let x = Int64.shift_left 1L (64 - m) in
    fanout_index_vec.(i) <- Int64.(bit_or fanout_index_vec.(i) x)

  method private update_index fanout_idx =
    let buf = Mstruct.of_bigarray ba in

    input_header buf;

    (* fanout table *)
    Log.debugf "c#update_index: entering fanout table";
    let start_ofs, sz, total_opt =
      if Int.(fanout_idx = 0) then begin
	0, Int32.to_int_exn (Mstruct.get_be_uint32 buf), None
      end
      else begin
	Mstruct.shift buf ((fanout_idx - 1) * 4);
	let sz0 = Int32.to_int_exn (Mstruct.get_be_uint32 buf) in
	let sz1 = Int32.to_int_exn (Mstruct.get_be_uint32 buf) in
	 sz0, sz1 - sz0, if Int.(fanout_idx = 255) then Some sz1 else None
      end 
    in
    let total = 
      match total_opt with
      | Some t -> t
      | None ->
	  Mstruct.shift buf ((254 - fanout_idx) * 4);
	  Int32.to_int_exn (Mstruct.get_be_uint32 buf)
    in
    let rest = total - start_ofs - sz in

    Log.debugf "c#update_index: fanout_idx:%d start_ofs:%d sz:%d" fanout_idx start_ofs sz;

    (* sha1 listing *)
    Log.debugf "c#update_index: entering sha1 listing";
    Mstruct.shift buf (start_ofs * 20);
    let sha1s = Array.create sz (SHA1.of_string "") in
    for i = 0 to sz - 1 do
      sha1s.(i) <- SHA1.input buf
    done;
    Mstruct.shift buf (rest * 20);

    (* crc checksums *)
    Log.debugf "c#update_index: entering crc checksums";
    Mstruct.shift buf (start_ofs * 4);
    let crcs =
      Array.foldi sha1s ~init:index.crcs
	~f:
	(fun i m sha1 ->
	  SHA1.Map.add m ~key:sha1 ~data:(Mstruct.get_be_uint32 buf)
	)
    in
    Mstruct.shift buf (rest * 4);

    (* packfile offsets *)
    Log.debugf "c#update_index: entering packfile offsets";

    (* Mstruct.shift buf (start_ofs * 4); *)
    let nconts0 = ref 0 in
    for i = 0 to start_ofs - 1 do
      begin
	match Int.(Mstruct.get_uint8 buf land 128) with
	| 0 -> ()
	| _ -> incr nconts0
      end;
      Mstruct.shift buf 3
    done;

    let conts = ref [] in
    let offsets =
      Array.foldi sha1s ~init:index.offsets
	~f:
	(fun i m sha1 ->
	  let more = 
	    match Int.(Mstruct.get_uint8 buf land 128) with
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
	    SHA1.Map.add m ~key:sha1 ~data:o
	)
    in
    Log.debugf "%d large packfile offsets to be read" (List.length !conts);
    (* Mstruct.shift buf (rest * 4); *)
    let nconts2 = ref 0 in
    for i = 0 to rest - 1 do
      begin
	match Int.(Mstruct.get_uint8 buf land 128) with
	| 0 -> ()
	| _ -> incr nconts2
      end;
      Mstruct.shift buf 3
    done;

    (* large packfile offsets *)
    Log.debugf "c#update_index: entering large packfile offsets";
    Mstruct.shift buf (!nconts0 * 8);
    let offsets =
      List.fold_left !conts ~init:offsets
	~f:
	(fun m i ->
	  let n = sha1s.(i) in
	  let o = Int64.to_int_exn (Mstruct.get_be_uint64 buf) in
	  SHA1.Map.add m ~key:n ~data:o
	) 
    in
    Mstruct.shift buf (!nconts2 * 8);

    (* pack checksum *)
    Log.debugf "c#update_index: entering pack checksum";
    let pack_checksum = SHA1.input buf in

    index <- { offsets; crcs; pack_checksum };

    self#set_loaded fanout_idx
  (* end of method update_index *)

      
end (* Pack_index.c *)
