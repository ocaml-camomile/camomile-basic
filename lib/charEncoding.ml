(* Copyright (C) 2001, 2002, 2003, Yamagata Yoriyuki *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

open OOChannel

let rec comp_sub_aux s1 i1 s2 i2 len =
  if len <= 0 then true else
  if s1.[i1] <> Bytes.get s2 i2 then false else
    comp_sub_aux s1 (i1 + 1) s2 (i2 + 1) (len - 1)

let comp_sub s1 i1 len1 s2 i2 len2 =
  if len1 <> len2 then false else
    comp_sub_aux s1 i1 s2 i2 len1

exception Malformed_code
exception Out_of_range

type 'a machine =
  {read : 'a -> unit;
   term : unit -> unit;}

let feed_string decoder s =
  for i = 0 to (String.length s) - 1 do
    decoder.read s.[i]
  done

type t =
  {name : string;
   make_decoder : UChar.t machine -> char machine;
   make_encoder : char machine -> UChar.t machine}

let null_umachine =
  {read = (fun _ -> ());
   term = (fun () -> ())}

type automatic_state =
    Detection of (t * (char machine)) list
  | Decoding of char machine

let accept_char m c =
  try m.read c; true with Malformed_code -> false

let automatic name encs def =
  let make_decoder um =
    let buf = Buffer.create 0 in
    let state = ref (Detection
                       (List.map (fun enc -> (enc, enc.make_decoder null_umachine)) encs))
    in
    let read c =
      match !state with
        Detection candidates ->
        Buffer.add_char buf c;
        let cs = List.filter (fun (_, m) -> accept_char m c) candidates in
        (match cs with
           [] -> raise Malformed_code
         | [(enc, _)] ->
           let m = enc.make_decoder um in
           feed_string m (Buffer.contents buf);
           state := Decoding m
         | _ -> state := Detection cs)
      | Decoding m -> m.read c
    in
    let term () =
      match !state with
        Detection ((enc, _) :: _) ->
        let m = enc.make_decoder um in
        feed_string m (Buffer.contents buf);
        m.term ()
      | Decoding m -> m.term ()
      | _ -> raise Malformed_code
    in
    {read = read; term = term}
  in
  {name = name; make_decoder = make_decoder; make_encoder = def.make_encoder}

let table = Hashtbl.create 0

let install name f =
  if Hashtbl.mem table name then
    failwith (name ^" has been already installed : CharEncoding.install")
  else begin
    Hashtbl.add table name (`P f);
  end

let new_enc name enc = install name (fun () -> enc)

let aliases : (string, string) Hashtbl.t = Hashtbl.create 0

let alias s1 s2 = Hashtbl.add aliases s1 s2

let of_name alias =
  let name = try Hashtbl.find aliases alias with Not_found -> alias in
  let rec look name =
    match Hashtbl.find table name with
      `P f ->
      let enc = f () in
      let b = Weak.create 1 in
      Weak.set b 0 (Some enc);
      Hashtbl.add table name (`W b);
      enc
    | `W b ->
      match Weak.get b 0 with
        None ->
        Hashtbl.remove table name;
        look name
      | Some x -> x
  in
  look name

let name_of enc = enc.name

let buf_machine buf =
  {read = (fun c -> Buffer.add_char buf c); term = fun () -> ()}

let recode_string ~in_enc ~out_enc s =
  let buf = Buffer.create (String.length s) in
  let encoder = out_enc.make_encoder (buf_machine buf) in
  let reader = in_enc.make_decoder encoder in
  feed_string reader s;
  reader.term ();
  Buffer.contents buf

let char_machine_of outchan =
  let b = Bytes.make 1024 '\000' in
  let pos = ref 0 in
  let read c =
    Bytes.set b !pos c;
    incr pos;
    if !pos >= 1024 then
      let n = outchan#output b 0 1024 in
      Bytes.blit b n b 0 (1024 - n);
      pos := 1024 - n
  in
  let flush () =
    let n = outchan#output b 0 !pos in
    if n < !pos then begin
      pos := !pos - n;
      failwith
        "CharEncoding.char_machine_of: \
         Cannot flush the entire buffer";
    end;
    outchan#flush ();
    pos := 0
  in
  let term () =
    flush ();
    outchan#close_out ()
  in
  {read = read; term = term}, flush

class uchar_output_channel_of
    enc
    (output : char_output_channel)
  : [UChar.t] obj_output_channel =
  let c, flush = char_machine_of output in
  let m = enc.make_encoder c in
  object
    method put u = m.read u
    method close_out = m.term
    method flush = flush
  end

class out_channel enc outchan =
  uchar_output_channel_of enc (new OOChannel.of_out_channel outchan)

let queueing q =
  let read u = Queue.add u q in
  let term () = () in
  {read = read; term = term}

class uchar_input_channel_of enc
    (input : char_input_channel)
  : [UChar.t] obj_input_channel =
  let q = Queue.create () in
  let b = Bytes.make 1024 '\000' in
  object(self : 'a)
    val m = enc.make_decoder (queueing q)
    val mutable term = false
    method get() =
      try Queue.take q with Queue.Empty ->
        if term then raise End_of_file else
          (try
             let len = input#input b 0 1024 in
             for i = 0 to len - 1 do m.read (Bytes.get b i) done
           with End_of_file ->
             m.term (); term <- true);
        self#get()
    method close_in =
      Queue.clear q; term <- true; input#close_in
  end

class in_channel enc inchan =
  uchar_input_channel_of enc (new OOChannel.of_in_channel inchan)

class in_channel_from_stream enc s =
  uchar_input_channel_of enc
    (new char_input_channel_of
      (new channel_of_stream s))

let fill_string s pos q =
  begin
    try while !pos < Bytes.length s do
        Bytes.set s !pos (Queue.take q);
        incr pos;
      done with Queue.Empty -> ()
  end;
  let read c =
    if !pos < Bytes.length s then begin
      Bytes.set s !pos c;
      incr pos;
    end else
      Queue.add c q
  in
  let term () = () in
  {read = read; term = term}

class convert_uchar_input enc (uinput : UChar.t obj_input_channel)
  : char_input_channel =
  let q = Queue.create () in
  object
    val eof = false
    method input s pos len =
      let p = ref pos in
      let m = enc.make_encoder (fill_string s p q) in
      try while !p < pos + len do
          m.read (uinput#get())
        done;
        !p - pos
      with End_of_file ->
        if eof then raise End_of_file else !p - pos
    method close_in () =
      uinput#close_in ();
      Queue.clear q;
  end

class convert_uchar_output enc (uoutput : UChar.t obj_output_channel)
  : char_output_channel =
  let m = enc.make_decoder {read = uoutput#put; term = uoutput#close_out} in
  object
    method output s pos len =
      for i = pos to pos + len - 1 do m.read (Bytes.get s i) done;
      len;
    method flush = uoutput#flush
    method close_out = m.term
  end

class convert_input ~in_enc ~out_enc input =
  convert_uchar_input out_enc (new uchar_input_channel_of in_enc input)

class convert_output ~in_enc ~out_enc output =
  convert_uchar_output in_enc (new uchar_output_channel_of out_enc output)

let ustream_of enc s = stream_of_channel (new in_channel_from_stream enc s)

class in_char_channel enc input : [char] obj_input_channel =
  let q = Queue.create () in
  object(self : 'a)
    val m = enc.make_encoder (queueing q)
    val q = q
    val mutable term = false
    method get() =
      try Queue.take q with Queue.Empty ->
        if term then raise End_of_file else
          (try let u = input#get() in m.read u with End_of_file ->
             m.term (); term <- true);
        self#get()
    method close_in () =
      Queue.clear q; term <- true; input#close_in ()
  end

class in_char_channel_from_ustream enc us =
  in_char_channel enc (new channel_of_stream us)

let char_stream_of enc us =
  stream_of_channel (new in_char_channel_from_ustream enc us)

module type Type =
sig
  type text
  val decode : t -> string -> text
  val encode : t -> text -> string
end

module Make (Text : UnicodeString.Type) =
struct
  type text = Text.t

  let ubuf_machine ubuf =
    {read = (fun u -> Text.Buf.add_char ubuf u); term = fun () -> ()}

  let feed_text encoder s =
    Text.iter encoder.read s

  let decode enc s =
    let buf = Text.Buf.create 0 in
    let m = enc.make_decoder (ubuf_machine buf) in
    feed_string m s;
    m.term ();
    Text.Buf.contents buf

  let encode enc s =
    let buf = Buffer.create (Text.length s) in
    let m = enc.make_encoder (buf_machine buf) in
    feed_text m s ;
    m.term ();
    Buffer.contents buf
end

(* Ascii *)
let _ =
  let make_decoder output_machine =
    let output = output_machine.read in
    let close = output_machine.term in
    let reader c =
      let code = Char.code c in
      if code >= 0x80 then raise Malformed_code else
        let u = UChar.chr_of_uint code in output u
    in
    let term () = close () in
    {read = reader; term = term}
  in
  let make_encoder output_machine =
    let output = output_machine.read in
    let close = output_machine.term in
    let reader u =
      let code = UChar.uint_code u in
      if code < 0 || code >= 0x80 then raise Out_of_range else
        output (Char.chr code)
    in
    let term () = close () in
    {read = reader; term = term}
  in
  let enc = fun () ->
    {name = "US-ASCII";
     make_decoder = make_decoder;
     make_encoder = make_encoder;}
  in begin
    install "US-ASCII" enc;
    install "USASCII" enc;
    install "ASCII" enc;
    install "ISO646US" enc;
    install "IBM367" enc;
    install "CP367" enc;
    install "ANSI_X3.4-1968" enc;
  end

(* ISO-8859-1, Latin-1 *)
let _ =
  let make_decoder output_machine =
    let output = output_machine.read in
    let close = output_machine.term in
    let reader c =
      let code = Char.code c in
      let u = UChar.chr_of_uint code in output u
    in
    let term () = close () in
    {read = reader; term = term}
  in
  let make_encoder output_machine =
    let output = output_machine.read in
    let close = output_machine.term in
    let reader u =
      let c =
        try (UChar.char_of u)
        with Invalid_argument _ -> raise Out_of_range
      in
      output c
    in
    let term () = close () in
    {read = reader; term = term}
  in
  let enc = fun () ->
    {name = "Latin-1";
     make_decoder = make_decoder;
     make_encoder = make_encoder;}
  in begin
    install "ISO-8859-1" enc;
    install "Latin-1" enc;
  end

(* UTF-8 *)

type utf8_decoder_state =
  {mutable remain : int; mutable cur : int}

let _ =
  let masq = 0b111111 in
  let make_decoder output_machine =
    let output = output_machine.read in
    let close = output_machine.term in
    let state = {remain = 0; cur = 0} in
    let reader c =
      let i = Char.code c in
      if state.remain = 0
      then				(*beginning of char*)
        if i <= 0x7f then output (UChar.chr_of_uint i) else
        if i >= 0xc2 && i <= 0xdf then
          begin state.remain <- 1; state.cur <- (i - 0xc0) end
        else if i >= 0xe0 && i <= 0xef then
          begin state.remain <- 2; state.cur <- (i - 0xe0) end
        else if i >= 0xf0 && i <= 0xf7 then
          begin state.remain <- 3; state.cur <- (i - 0xf0) end
        else if i >= 0xf8 && i <= 0xfb then
          begin state.remain <- 4; state.cur <- (i - 0xf8) end
        else if i >= 0xfc && i <= 0xfd then
          begin state.remain <- 5; state.cur <- (i - 0xfc) end
        else raise Malformed_code
      else
      if i < 0x80 then raise Malformed_code else
        let i' = i - 0x80 in
        let a = (state.cur lsl 6) + i' in
        (* reject unnecessary long encoding *)
        if a = 0 then raise Malformed_code else
          state.remain <- state.remain - 1;
        if state.remain = 0 then output (UChar.chr_of_uint a) else
          state.cur <- a
    in
    let term () = close () in
    {read = reader; term = term}
  in
  let make_encoder output_machine =
    let output = output_machine.read in
    let close = output_machine.term in
    let reader u =
      let k = UChar.uint_code u in
      if k >= 0 && k <= 0x7f then output (Char.chr k) else
      if k >= 0x80 && k <= 0x7ff then
        let c0 = Char.chr (0xc0 + (k lsr 6)) in
        let c1 = Char.chr (0x80 + (k land masq)) in
        begin output c0; output c1; end
      else if k >= 0x800 && k <= 0xffff then
        let c0 = Char.chr (0xe0 + (k lsr 12)) in
        let c1 = Char.chr (0x80 + ((k lsr 6) land masq)) in
        let c2 = Char.chr (0x80 + (k land masq)) in
        begin output c0; output c1; output c2 end
      else if k >= 0x10000 && k <= 0x1fffff then
        let c0 = Char.chr (0xf0 + (k lsr 18)) in
        let c1 = Char.chr (0x80 + ((k lsr 12) land masq)) in
        let c2 = Char.chr (0x80 + ((k lsr 6) land masq)) in
        let c3 = Char.chr (0x80 + (k land masq)) in
        begin output c0; output c1; output c2; output c3 end
      else if k >= 0x200000 && k <= 0x3ffffff then
        let c0 = Char.chr (0xf8 + (k lsr 24)) in
        let c1 = Char.chr (0x80 + ((k lsr 18) land masq)) in
        let c2 = Char.chr (0x80 + ((k lsr 12) land masq)) in
        let c3 = Char.chr (0x80 + ((k lsr 6) land masq)) in
        let c4 = Char.chr (0x80 + (k land masq)) in
        begin output c0; output c1; output c2; output c3; output c4 end
      else if k >= 0x4000000 || k < 0 then
        let c0 = Char.chr (0xfc + (k lsr 30)) in
        let c1 = Char.chr (0x80 + ((k lsr 24) land masq)) in
        let c2 = Char.chr (0x80 + ((k lsr 18) land masq)) in
        let c3 = Char.chr (0x80 + ((k lsr 12) land masq)) in
        let c4 = Char.chr (0x80 + ((k lsr 6) land masq)) in
        let c5 = Char.chr (0x80 + (k land masq)) in
        begin
          output c0; output c1; output c2; output c3; output c4; output c5
        end
      else raise Out_of_range
    in
    let term () = close () in
    {read = reader; term = term}
  in
  let enc = fun () ->
    {name = "UTF-8";
     make_decoder = make_decoder;
     make_encoder = make_encoder;}
  in begin
    install "UTF-8" enc;
  end

(* UTF-16 *)

type ucs2_machine =
  {read2 : int -> unit;
   term2 : unit -> unit}

type ucs2_buf =
  {mutable first_char : bool;
   mutable buf : int}

let char_machine_be m =
  let state = {first_char = true; buf = 0} in
  let read c =
    if state.first_char
    then begin state.buf <- (Char.code c); state.first_char <- false; end
    else begin
      m.read2 ((state.buf lsl 8) lor (Char.code c));
      state.first_char <- true;
    end
  in
  let term () = m.term2 () in
  {read = read; term = term}

let char_machine_le m =
  let state = {first_char = true; buf = 0} in
  let read c =
    if state.first_char
    then begin state.buf <- (Char.code c); state.first_char <- false; end
    else begin
      m.read2 (((Char.code c) lsl 8) lor state.buf);
      state.first_char <- true;
    end
  in
  let term () = m.term2 () in
  {read = read; term = term}

let be_outmachine m =
  let read i =
    m.read (Char.chr (i lsr 8));
    m.read (Char.chr (i land 255))
  in {read2 = read; term2 = m.term}

let le_outmachine m =
  let read i =
    m.read (Char.chr (i land 255));
    m.read (Char.chr (i lsr 8))
  in {read2 = read; term2 = m.term}

type utf16_decoder_state =
  {mutable surrogated : bool;
   mutable buf : int}

let _ =
  let make_decoder m =
    let output = m.read in
    let close = m.term in
    let state = {surrogated = false; buf = 0} in
    let read i =
      if state.surrogated
      then
        if i >= 0xdc00 && i <= 0xdfff then
          let i' = (state.buf - 0xd800) lsl 10 + (i - 0xdc00) + 0x10000 in
          begin output (UChar.chr_of_uint i'); state.surrogated <- false end
        else raise Malformed_code
      else
      if i = 0xfeff then () else	(*BOM is ignored*)
      if i <= 0xd7ff || (i >= 0xe000 && i <= 0xfffd) then
        output (UChar.chr_of_uint i)
      else if i >= 0xd800 && i <= 0xdbff then
        begin state.surrogated <- true; state.buf <- i end
      else raise Malformed_code
    in
    let term = close in
    {read2 = read; term2 = term}
  in
  let make_encoder m =
    let output = m.read2 in
    let close = m.term2 in
    output 0xfeff;
    let read u =
      let i = UChar.uint_code u in
      if i >= 0x0 && i < 0xd800 || i >= 0xe000 && i < 0x10000
      then output i
      else if i >= 0x10000 && i <= 0x10ffff then
        let i1 = (i - 0x10000) lsr 10 + 0xd800 in
        let i2 = (i - 0x10000) land 0x3ff + 0xdc00 in
        output i1; output i2
      else raise Out_of_range
    in
    let term = close in
    {read = read; term = term}
  in
  let make_decoder_be m = char_machine_be (make_decoder m) in
  let make_encoder_be m = make_encoder (be_outmachine m) in
  let make_decoder_le m = char_machine_le (make_decoder m) in
  let make_encoder_le m = make_encoder (le_outmachine m) in

  let enc_be =
    {name = "UTF-16BE";
     make_decoder = make_decoder_be;
     make_encoder = make_encoder_be;}
  in
  let enc_le =
    {name = "UTF-16LE";
     make_decoder = make_decoder_le;
     make_encoder = make_encoder_le;}
  in

  let enc_unknown =
    fun () -> automatic "UTF-16" [enc_be; enc_le] enc_be in

  begin
    install "UTF-16BE" (fun () -> enc_be);
    install "UTF-16LE" (fun () -> enc_le);
    install "UTF-16" enc_unknown
  end

(* UCS-4, UTF-32, UTF-32BE, UTF-32LE*)

module UTF32 =
struct

  type ucs4_machine =
    {read4 : int -> unit;
     term4 : unit -> unit}

  type ucs4_buf =
    {mutable count : int;
     mutable buf : int}

  let char_machine_be m =
    let state = {count = 0; buf = 0} in
    let read c =
      let i = Char.code c in
      if state.count = 0 && i > 0x7f then raise Malformed_code else begin
        state.buf <- (state.buf lsl 8) lor i;
        state.count <- state.count + 1;
        if state.count = 4 then begin
          m.read4 state.buf;
          state.count <- 0; state.buf <- 0 end
        else ()
      end
    in
    let term () = m.term4 () in
    {read = read; term = term}

  let char_machine_le m =
    let state = {count = 0; buf = 0} in
    let read c =
      let i = Char.code c in
      if state.count = 3 && i > 0x7f then raise Malformed_code else begin
        state.buf <- (i lsl (8 * state.count)) lor state.buf;
        state.count <- state.count + 1;
        if state.count = 4 then begin
          m.read4 state.buf;
          state.count <- 0; state.buf <- 0 end
        else ()
      end
    in
    let term () = m.term4 () in
    {read = read; term = term}

  let be_outmachine m =
    let read i =
      m.read (Char.chr (i lsr 24));
      m.read (Char.chr ((i lsr 16) land 255));
      m.read (Char.chr ((i lsr 8) land 255));
      m.read (Char.chr (i land 255))
    in {read4 = read; term4 = m.term}

  let le_outmachine m =
    let read i =
      m.read (Char.chr (i land 255));
      m.read (Char.chr ((i lsr 8) land 255));
      m.read (Char.chr ((i lsr 16) land 255));
      m.read (Char.chr (i lsr 24))
    in {read4 = read; term4 = m.term}

  let make_ucs4_decoder m =
    let read n =
      m.read (UChar.chr_of_uint n)
    in
    let term () = m.term () in
    {read4 = read; term4 = term}

  let make_ucs4_encoder m =
    let read u =
      let n = UChar.uint_code u in
      m.read4 n
    in
    let term () = m.term4 () in
    {read = read; term = term}

  let make_utf32_decoder m =
    let read n =
      if n = 0xfeff then () else	(*BOM is ignored*)
      if n > 0x10ffff || n < 0 || n = 0xfffe then raise Malformed_code else
        m.read (UChar.chr_of_uint n)
    in
    let term () = m.term () in
    {read4 = read; term4 = term}

  let make_utf32_encoder m =
    m.read4 0xfeff;
    let read u =
      let n = UChar.uint_code u in
      if n > 0x10ffff || n < 0 || n = 0xfffe then raise Out_of_range else
        m.read4 n
    in
    let term () = m.term4 () in
    {read = read; term = term}

  let make_utf32_be_decoder m =
    char_machine_be (make_utf32_decoder m)

  let make_utf32_le_decoder m =
    char_machine_le (make_utf32_decoder m)

  let make_utf32_be_encoder m =
    make_utf32_encoder (be_outmachine m)

  let make_utf32_le_encoder m =
    make_utf32_encoder (le_outmachine m)

  (* 4-bytes encoding for unicode.  All 31-bits code points are allowed.
   * ISO 10646-1 doesn't specify endianess.  We use big endian ordering
   * without BOM.
  *)
  let ucs4 =
    let make_decoder m = char_machine_be (make_ucs4_decoder m) in
    let make_encoder m = make_ucs4_encoder (be_outmachine m) in
    {name = "UCS-4";
     make_decoder = make_decoder;
     make_encoder = make_encoder}

  (* The same as UCS-4, but range is limited to 21-bits code points. *)
  let utf32_be =
    let make_decoder m = make_utf32_be_decoder m in
    let make_encoder m = make_utf32_be_encoder m in
    {name = "UTF-32BE";
     make_decoder = make_decoder;
     make_encoder = make_encoder}

  (* Little endian order. *)
  let utf32_le =
    let make_decoder m = make_utf32_le_decoder m in
    let make_encoder m = make_utf32_le_encoder m in
    {name = "UTF-32LE";
     make_decoder = make_decoder;
     make_encoder = make_encoder}

  (* UTF-32 with unknown endianness. *)
  let utf32 = fun () ->
    automatic "UTF-32" [utf32_be; utf32_le] utf32_be

  let init () =
    install "UCS-4" (fun () -> ucs4);
    install "UTF-32BE" (fun () -> utf32_be);
    install "UTF-32LE" (fun () -> utf32_le);
    install "UTF-32" utf32

end

let _ = UTF32.init ()

(* shortcuts *)
let ascii = of_name "US-ASCII"
let latin1 = of_name "Latin-1"
let utf8 = of_name "UTF-8"
let utf16 = of_name "UTF-16"
let utf16be = of_name "UTF-16BE"
let utf16le = of_name "UTF-16LE"
let utf32 = of_name "UTF-32"
let utf32be = of_name "UTF-32BE"
let utf32le = of_name "UTF-32LE"
let ucs4 = of_name "UCS-4"
