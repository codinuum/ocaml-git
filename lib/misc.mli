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

(** Miscellaneous functions. *)

open Core_kernel.Std

(** {2 Bounded parallelism} *)

val list_iter_p: ?width:int -> ('a -> unit Lwt.t) -> 'a list -> unit Lwt.t
(** Same as [List_lwt.iter_p] but using a maximum width of
    [width]. The default width is 50. *)

val list_map_p: ?width:int -> ('a -> 'b Lwt.t) -> 'a list -> 'b list Lwt.t
(** Same as [List_lwt.map_p] but using a maximum width of [width]. The
    default width is 50. *)

(** {2 Hexa encoding} *)

val hex_encode: string -> string
(** Encode a string to base16. *)

val hex_decode: string -> string
(** Decode a string from base16. *)

val buffer_contents: Bigbuffer.t -> Bigstring.t
(** zero-copy buffer contents. *)

val with_bigbuffer: (Bigbuffer.t -> unit) -> Bigstring.t
(** Create a temporarybuffer, apply a function to append stuff to
    it, and return the buffer contents as a bigstring. *)

val with_buffer: (Bigbuffer.t -> unit) -> string
(** Create a temporary buffer, apply a function to append stuff to it,
    and return the buffer contents. *)

(** {2 Zlib Compression} *)

val inflate_bigstring: Bigstring.t -> Bigstring.t
(** Inflate a buffer. *)

val deflate_bigstring: Bigstring.t -> Bigstring.t
(** Deflate a big string. *)

val inflate_mstruct: Mstruct.t -> Mstruct.t
(** Inflate a buffer. *)

val deflate_mstruct: Mstruct.t -> Mstruct.t
(** Deflate a buffer. *)

(** {2 CRC-32} *)

val crc32: string -> int32
(** Return the CRC-32 value of a bigstring. *)

(** {2 Maps} *)

val map_rev_find: ('key, 'value, 'cmp) Map.t -> 'value -> 'key option
(** Reverse of [Map.find]. *)

(** {2 Marshaling helpers} *)

val add_be_uint32: Bigbuffer.t -> int32 -> unit

val input_key_value: Mstruct.t -> key:string -> (Mstruct.t -> 'a) -> 'a

val sp: char
val nul: char
val lf: char
val lt: char
val gt: char

module OP: sig

  val (/): string -> string -> string
  (** Same as [Filename.concat]. *)

end
