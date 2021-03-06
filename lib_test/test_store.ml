(*
 * Copyright (c) 2013 Thomas Gazagnaire <thomas@gazagnaire.org>
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

open OUnit
open Test_common
open Lwt
open Core_kernel.Std
open Git

type t = {
  name : string;
  init : unit -> unit Lwt.t;
  clean: unit -> unit Lwt.t;
  store: (module Store.S);
}

let unit () =
  return_unit

let log_level = Log.get_log_level ()

module Make (Store: Store.S) = struct

  module Common = Make(Store)
  open Common
  module Search = Search.Make(Store)

  let () = Log.(set_log_level INFO)

  let run x test =
    Log.set_log_level log_level;
    try Lwt_unix.run (x.init () >>= test >>= x.clean)
    with e ->
      Lwt_unix.run (x.clean ());
      raise e

  let long_random_string = Cryptokit.(Random.string (Random.device_rng "/dev/urandom") 1024)
  let v1 = Value.blob (Blob.of_string long_random_string)
  let kv1 = Value.sha1 v1

  let v2 = Value.blob (Blob.of_string "")
  let kv2 = Value.sha1 v2

  (* Create a node containing t1 -a-> v1 *)
  let t1 = Value.tree ([
      { Tree.perm = `Normal;
        name = "a";
        node = kv1 }
    ])
  let kt1 = Value.sha1 t1

  (* Create the tree t2 -b-> t1 -a-> v1 *)
  let t2 = Value.tree ([
      { Tree.perm = `Dir;
        name = "b";
        node = kt1 }
    ])
  let kt2 = Value.sha1 t2

  (* Create the tree t3 -a-> t2 -b-> t1 -a-> v1 *)
  let t3 = Value.tree ([
      { Tree.perm = `Dir;
        name = "a";
        node = kt2; }
    ])
  let kt3 = Value.sha1 t3

  (* Create the tree t4 -a-> t2 -b-> t1 -a-> v1
                       \-c-> v2 *)
  let t4 = Value.tree ([
      { Tree.perm = `Exec;
        name = "c";
        node = kv2; };
      { Tree.perm = `Dir;
        name = "a";
        node = kt2; }
    ])
  let kt4 = Value.sha1 t4

  let john_doe = User.({
      name  = "John Doe";
      email = "jon@doe.com";
      date  = "today";
    })

  (* c1 : t2 *)
  let c1 = Value.commit {
      Commit.tree = SHA1.to_tree kt2;
      parents     = [];
      author      = john_doe;
      committer   = john_doe;
      message     = "hello r1!";
    }
  let kc1 = Value.sha1 c1

  (* c1 -> c2 : t4 *)
  let c2 = Value.commit {
      Commit.tree = SHA1.to_tree kt4;
      parents     = [SHA1.to_commit kc1];
      author      = john_doe;
      committer   = john_doe;
      message     = "hello r1!"
    }
  let kc2 = Value.sha1 c2

  (* tag1: c1 *)
  let tag1 = Value.tag {
      Tag.sha1 = kc1;
      typ      = Object_type.Commit;
      tag      = "foo";
      tagger   = john_doe;
      message  = "Ho yeah!";
    }
  let ktag1 = Value.sha1 tag1

  (* tag2: c2 *)
  let tag2 = Value.tag {
      Tag.sha1 = kc2;
      typ      = Object_type.Commit;
      tag      = "bar";
      tagger   = john_doe;
      message  = "Hahah!";
    }
  let ktag2 = Value.sha1 tag2

  (* r1: t4 *)
  let r1 = Reference.of_string "refs/origin/head"

  (* r2: c2 *)
  let r2 = Reference.of_string "refs/upstream/head"

  let check_write t name k v =
    Store.write t v    >>= fun k' ->
    assert_key_equal (name ^ "-key-1") k k';
    Store.read_exn t k >>= fun v' ->
    assert_value_equal name v v';
    Store.write t v'   >>= fun k'' ->
    assert_key_equal (name ^ "-key-2") k k'';
    return_unit

  let check_find t name k path e =
    Search.find t k path >>= fun k' ->
    assert_key_opt_equal (name ^ "-find") (Some e) k';
    return_unit

  let create () =
    Store.create ~root:"test-db" () >>= fun t  ->
    Store.clear t                   >>= fun () ->
    Lwt_list.iter_p
      (fun v -> Store.write t v >>= fun _ -> return_unit)
      [
        v1; v2;
        t1; t2; t3; t4;
        c1; c2
      ] >>= fun () ->
    return t

  let is_ typ t k =
    Store.read t k >>= function
    | None   -> return false
    | Some v ->
      return (typ = Value.type_of v)

  let check_keys t name typ expected =
    Store.list t                     >>= fun ks ->
    Lwt_list.filter_p (is_ typ t) ks >>= fun ks ->
    return (assert_keys_equal name expected ks)

  let test_blobs x () =
    let test () =
      create ()                 >>= fun t     ->
      check_write t "v1" kv1 v1 >>= fun () ->
      check_write t "v2" kv2 v2 >>= fun () ->

      check_keys t "blobs" Object_type.Blob [kv1; kv2] >>= fun () ->
      return_unit
    in
    run x test

  let test_trees x () =
    let test () =
      create ()                 >>= fun t  ->
      check_write t "t1" kt1 t1 >>= fun () ->
      check_write t "t2" kt2 t2 >>= fun () ->
      check_write t "t3" kt3 t3 >>= fun () ->
      check_write t "t4" kt4 t4 >>= fun () ->

      check_find t "kt1:a"     kt1 ["a"]         kv1 >>= fun () ->
      check_find t "kt2:b"     kt2 ["b"]         kt1 >>= fun () ->
      check_find t "kt2:b/a"   kt2 ["b";"a"]     kv1 >>= fun () ->
      check_find t "kt3:a"     kt3 ["a"]         kt2 >>= fun () ->
      check_find t "kt3:a/b"   kt3 ["a";"b"]     kt1 >>= fun () ->
      check_find t "kt3:a/b/a" kt3 ["a";"b";"a"] kv1 >>= fun () ->
      check_find t "kt4:c"     kt4 ["c"]         kv2 >>= fun () ->

      check_keys t "trees" Object_type.Tree [kt1; kt2; kt3; kt4] >>= fun () ->

      return_unit
    in
    run x test

  let test_commits x () =
    let test () =
      create ()                 >>= fun t   ->
      check_write t "c1" kc1 c1 >>= fun () ->
      check_write t "c2" kc2 c2 >>= fun () ->

      check_find t "c1:b"     kc1 ["";"b"]         kt1 >>= fun () ->
      check_find t "c1:b/a"   kc1 ["";"b";"a"]     kv1 >>= fun () ->
      check_find t "c2:a/b/a" kc2 ["";"a";"b";"a"] kv1 >>= fun () ->
      check_find t "c2:c"     kc2 ["";"c"]         kv2 >>= fun () ->

      check_keys t "commits" Object_type.Commit [kc1; kc2] >>= fun () ->

      return_unit
    in
    run x test

  let test_tags x () =
    let test () =
      create () >>= fun t   ->
      check_write t "tag1" ktag1 tag1 >>= fun () ->
      check_write t "tag2" ktag2 tag2 >>= fun () ->

      check_find t "tag1:b" ktag1 ["foo";"";"b"] kt1 >>= fun () ->
      check_find t "tag2:a" ktag2 ["bar";"";"a"] kt2 >>= fun () ->
      check_find t "tag2:c" ktag2 ["bar";"";"c"] kv2 >>= fun () ->

      check_keys t "tags" Object_type.Tag [ktag1; ktag2] >>= fun () ->

      return_unit
    in
    run x test

  let test_refs x () =
    let test () =
      create () >>= fun t ->
      let c = SHA1.to_commit in
      let ko = function
        | None   -> None
        | Some x -> Some (SHA1.of_commit x) in
      Store.write_reference t r1 (c kt4) >>= fun ()   ->
      Store.read_reference t r1          >>= fun kt4' ->
      assert_key_opt_equal "r1" (Some kt4) (ko kt4');

      Store.write_reference t r2 (c kc2) >>= fun ()   ->
      Store.read_reference t r2          >>= fun kc2' ->
      assert_key_opt_equal "r2" (Some kc2) (ko kc2');

      Store.references t                 >>= fun rs   ->
      assert_refs_equal "refs" [r1; r2] rs;

      return_unit
    in
    run x test

  let test_index x () =
    if x.name = "FS" then
      let test () =
        Git_unix.rec_files "." >>= fun files ->
        Lwt_list.map_p (fun file ->
            let blob =
              file
              |> Git_unix.read_file
              |> Bigstring.to_string
              |> Blob.of_string in
            Git_fs.entry_of_file file `Normal blob
          ) files >>= fun entries ->
        let entries = List.filter_map ~f:(fun x -> x) entries in
        let cache = { Cache.entries; extensions = [] } in
        let buf = Misc.with_bigbuffer (fun buf -> Cache.add buf cache) in
        let cache2 = Cache.input (Mstruct.of_bigarray buf) in
        assert_cache_equal "cache" cache cache2;
        return_unit
      in
      run x test

  let test_packs x () =
    if x.name = "FS" then
      let test () =
        Git_unix.files "data/" >>= fun files ->
        if files = [] then
          failwith "Please run that test in lib_test/";
        let files = List.filter ~f:(fun file ->
            String.is_suffix file ~suffix:".pack"
          ) files in
        let files = List.map ~f:(fun file ->
            let name = String.chop_prefix_exn file ~prefix:"data/pack-" in
            let name = String.chop_suffix_exn name ~suffix:".pack" in
            file, "data/pack-" ^ name ^ ".idx"
          ) files in
        List.iter ~f:(fun (pack, index) ->

            (* basic serialization of index files *)
            let istr1 = Git_unix.read_file index in
            let i1    = Pack_index.input (Mstruct.of_bigarray istr1) in
            let istr2 = Misc.with_bigbuffer (fun buf -> Pack_index.add buf i1) in
            let i2    = Pack_index.input (Mstruct.of_bigarray istr2) in
            assert_pack_index_equal "pack-index" i1 i2;

            (* basic serialization of pack files *)
            let pstr1 = Git_unix.read_file pack in
            let rp1   = Pack.Raw.input (Mstruct.of_bigarray pstr1) ~index:None in
            let rp1'  = Pack.Raw.input (Mstruct.of_bigarray pstr1) ~index:(Some i1) in
            assert_raw_pack_equal "raw-pack" rp1 rp1';

            let pstr2 = Misc.with_bigbuffer (fun buf -> Pack.Raw.add buf rp1) in
            let rp2   = Pack.Raw.input (Mstruct.of_bigarray pstr2) ~index:None in
            assert_pack_equal "pack" (Pack.to_pic rp1) (Pack.to_pic rp2);

            let i3 = Pack.Raw.index rp1 in
            assert_pack_index_equal "raw-pack-->>--pack-index" i1 i3;

          ) files;

        return_unit
      in
      run x test

end

let suite (speed, x) =
  let (module S) = x.store in
  let module T = Make(S) in
  x.name,
  [
    "Basic operations on blobs"       , speed, T.test_blobs    x;
    "Basic operations on trees"       , speed, T.test_trees    x;
    "Basic operations on commits"     , speed, T.test_commits  x;
    "Basic operations on tags"        , speed, T.test_tags     x;
    "Basic operations on references"  , speed, T.test_refs     x;
    "Basic operations on index"       , speed, T.test_index    x;
    "Basic operations on pack files"  , speed, T.test_packs    x;
  ]

let run name tl =
  let tl = List.map ~f:suite tl in
  Alcotest.run name tl
