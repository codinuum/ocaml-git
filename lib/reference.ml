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

open Core_kernel.Std
module Log = Log.Make(struct let section = "reference" end)

include String

let compare x y =
  match x, y with
  | "HEAD", "HEAD" -> 0
  | "HEAD", _      -> (-1)
  | _     , "HEAD" -> 1
  | _     , _      -> compare x y

let head = "HEAD"

type head_contents =
  | SHA1 of SHA1.Commit.t
  | Ref of t

let is_head x =
  String.(head = x)

let head_contents refs sha1 =
  let refs = Map.remove refs "HEAD" in
  match Misc.map_rev_find refs sha1 with
  | None   -> SHA1 sha1
  | Some r -> Ref r
