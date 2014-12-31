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

(* XXX: we only implement index file cache format V2 *)

open Lwt
open Core_kernel.Std
module Log = Log.Make(struct let section = "cache" end)

type time = {
  lsb32: Int32.t;
  nsec : Int32.t;
} with bin_io, compare, sexp

type mode = [
    `Normal
  | `Exec
  | `Link
  | `Gitlink
] with bin_io, compare, sexp

type stat_info = {
  ctime: time;
  mtime: time;
  dev  : Int32.t;
  inode: Int32.t;
  mode : mode;
  uid  : Int32.t;
  gid  : Int32.t;
  size : Int32.t;
} with bin_io, compare, sexp

type entry = {
  stats : stat_info;
  id    : SHA1.t;
  stage : int;
  name  : string;
} with bin_io, compare, sexp

let pretty_entry t =
  sprintf
    "%s\n\
    \  ctime: %ld:%ld\n\
    \  mtime: %ld:%ld\n\
    \  dev: %ld\tino: %ld\n\
    \  uid: %ld\tgid: %ld\n\
    \  size: %ld\tflags: %d\n"
    t.name
    t.stats.ctime.lsb32 t.stats.ctime.nsec
    t.stats.mtime.lsb32 t.stats.mtime.nsec
    t.stats.dev t.stats.inode
    t.stats.uid t.stats.gid
    t.stats.size t.stage

module T = struct
  type t = {
    entries   : entry list;
    extensions: (Int32.t * string) list;
  }
  with bin_io, compare, sexp
  let hash (t: t) = Hashtbl.hash t
  include Sexpable.To_stringable (struct type nonrec t = t with sexp end)
  let module_name = "Cache"
end
include T
include Identifiable.Make (T)

let pretty t =
  let buf = Buffer.create 1024 in
  List.iter ~f:(fun e ->
      Buffer.add_string buf (pretty_entry e)
    ) t.entries;
  Buffer.contents buf

let input_time buf =
  let lsb32 = Mstruct.get_be_uint32 buf in
  let nsec = Mstruct.get_be_uint32 buf in
  { lsb32; nsec }

let output_time buf t =
  Mstruct.set_be_uint32 buf t.lsb32;
  Mstruct.set_be_uint32 buf t.nsec

let input_mode buf =
  let _zero = Mstruct.get_be_uint16 buf in
  (* XX: check that _zero is full of 0s *)
  let n = Mstruct.get_be_uint16 buf in
  match Int32.(n lsr 12) with
  | 0b1010 -> `Link
  | 0b1110 -> `Gitlink
  | 0b1000 ->
    begin match Int32.(n land 0x1FF) with
      | 0o755 -> `Exec
      | 0o644 -> `Normal
      | d     -> Mstruct.parse_error_buf buf "mode: invalid permission (%d)" d
    end
  | m -> Mstruct.parse_error_buf buf "mode: invalid (%d)" m

let output_mode buf t =
  let n = match t with
    | `Exec    -> 0o1000__000__111_101_101
    | `Normal  -> 0b1000__000__110_100_100
    | `Link    -> 0b1010__000__000_000_000
    | `Gitlink -> 0b1110__000__000_000_000 in
  Mstruct.set_be_uint16 buf 0;
  Mstruct.set_be_uint16 buf n

let input_stat_info buf =
  Log.debug "input_stat_info";
  let ctime = input_time buf in
  let mtime = input_time buf in
  let dev = Mstruct.get_be_uint32 buf in
  let inode = Mstruct.get_be_uint32 buf in
  let mode = input_mode buf in
  let uid = Mstruct.get_be_uint32 buf in
  let gid = Mstruct.get_be_uint32 buf in
  let size = Mstruct.get_be_uint32 buf in
  { mtime; ctime; dev; inode; mode; uid; gid; size }

let add_stat_info buf t =
  output_time buf t.ctime;
  output_time buf t.mtime;
  let uint32 = Mstruct.set_be_uint32 buf in
  uint32 t.dev;
  uint32 t.inode;
  output_mode buf t.mode;
  uint32 t.uid;
  uint32 t.gid;
  uint32 t.size

let input_entry buf =
  Log.debug "input_entry";
  let offset0 = Mstruct.offset buf in
  let stats = input_stat_info buf in
  let id = SHA1.input buf in
  let stage, len =
    let i = Mstruct.get_be_uint16 buf in
    (i land 0x3000) lsr 12,
    (i land 0x0FFF) in
  Log.debug "stage:%d len:%d" stage len;
  let name = Mstruct.get_string buf len in
  Mstruct.shift buf 1;
  let bytes = Mstruct.offset buf - offset0 in
  let padding = match bytes mod 8 with
    | 0 -> 0
    | n -> 8-n in
  Mstruct.shift buf padding;
  Log.debug "name: %s id: %s bytes:%d padding:%d"
    name (SHA1.to_hex id) bytes padding;
  { stats; id; stage; name }

let add_entry buf t =
  Log.debug "add_entry";
  let len = 63 + String.length t.name in
  let pad = match len mod 8 with
    | 0 -> 0
    | n -> 8-n in
  let mstr = Mstruct.create (len+pad) in
  add_stat_info mstr t.stats;
  Mstruct.set_string mstr (SHA1.to_string t.id);
  let flags = (t.stage lsl 12 + String.length t.name) land 0x3FFF in
  Mstruct.set_be_uint16 mstr flags;
  Mstruct.set_string mstr t.name;
  Mstruct.set_string mstr (String.make (1+pad) '\x00');
  let str = mstr |> Mstruct.to_bigarray |> Bigstring.to_string in
  Bigbuffer.add_string buf str

let input_extensions _buf =
  (* TODO: actually read the extension contents *)
  []

let input buf =
  let offset = Mstruct.offset buf in
  let total_length = Mstruct.length buf in
  let header = Mstruct.get_string buf 4 in
  if String.(header <> "DIRC") then
    Mstruct.parse_error_buf buf "%s: wrong cache header." header;
  let version = Mstruct.get_be_uint32 buf in
  if Int32.(version <> 2l) then
    failwith (Printf.sprintf "Only cache version 2 is supported (%ld)" version);
  let n = Mstruct.get_be_uint32 buf in
  Log.debug "input: %ld entries (%db)" n (Mstruct.length buf);
  let entries =
    let rec loop acc n =
      if Int32.(n = 0l) then List.rev acc
      else
        let entry = input_entry buf in
        loop (entry :: acc) Int32.(n - 1l) in
    loop [] n in
  let extensions = input_extensions buf in
  let length = Mstruct.offset buf - offset in
  if Int.(length <> total_length - 20) then (
    eprintf "Cache.input: more data to read! (total:%d current:%d)"
      (total_length - 20) length;
    failwith "Cache.input"
  );
  let actual_checksum =
    buf
    |> Mstruct.to_bigarray
    |> Bigstring.To_string.sub ~pos:offset ~len:length
    |> SHA1.create in
  let checksum = SHA1.input buf in
  if SHA1.(actual_checksum <> checksum) then (
    eprintf "Cach.input: wrong checksum";
    failwith "Cache.input"
  );
  { entries; extensions }

let add buf t =
  let str = Misc.with_buffer (fun buf ->
      let n = List.length t.entries in
      Log.debug "add %d entries" n;
      let header = Mstruct.create 12 in
      Mstruct.set_string header "DIRC";
      Mstruct.set_be_uint32 header 2l;
      Mstruct.set_be_uint32 header (Int32.of_int_exn n);
      let str = header |> Mstruct.to_bigarray |> Bigstring.to_string in
      Bigbuffer.add_string buf str;
      List.iter ~f:(add_entry buf) t.entries;
    ) in
  let sha1 = SHA1.create str in
  Bigbuffer.add_string buf str;
  Bigbuffer.add_string buf (SHA1.to_string sha1)
