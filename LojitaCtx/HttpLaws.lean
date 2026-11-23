import LojitaCtx.NetSandbox

set_option maxRecDepth 8192

namespace LojitaCtx.NetLaws
open Terminal NetSandbox

private theorem andLeft {a b : Bool} (h : (a && b) = true) : a = true :=
  (Bool.and_eq_true_iff.mp h).1

private theorem andRight {a b : Bool} (h : (a && b) = true) : b = true :=
  (Bool.and_eq_true_iff.mp h).2

private theorem notTrue {b : Bool} (h : (!b) = true) : b = false := by cases b <;> simp_all

def NoCR : Bytes → Bool :=
  FsSandbox.all fun b => !(13 == b.toNat)

def NoCRLF : Bytes → Bool :=
  FsSandbox.all fun b => !(13 == b.toNat) && !(10 == b.toNat)

def TokenByte (b : Byte) : Bool :=
  !isAsciiSpaceByte b &&
    (!(13 == b.toNat) && !(10 == b.toNat))

def NonEmptyBytes : Bytes → Bool
  | [] => false
  | _ :: _ => true

def ValidTokenBytes (bs : Bytes) : Bool :=
  NonEmptyBytes bs && FsSandbox.all TokenByte bs

def ValidHttpToken (s : String) : Bool :=
  ValidTokenBytes (bytes s)

private theorem allTokenNoCR : ∀ (bs : Bytes), FsSandbox.all TokenByte bs = true → NoCR bs = true
  | [], _ => rfl
  | b :: bs, ok => by
    have htb : TokenByte b = true := andLeft ok
    have hbs : FsSandbox.all TokenByte bs = true := andRight ok
    have h13 : Bool.not (13 == b.toNat) = true := andLeft (andRight htb)
    simp only [NoCR, FsSandbox.all, h13, Bool.true_and]
    exact allTokenNoCR bs hbs
termination_by structural bs _ => bs

private theorem noCRAppend :
    ∀ (xs ys : Bytes), NoCR xs = true → NoCR ys = true → NoCR (xs ++ ys) = true
  | [], _, _, okY => okY
  | x :: xs, ys, okX, okY => by
    have hx : Bool.not (13 == UInt8.toNat x) = true := andLeft okX
    have hxs : NoCR xs = true := andRight okX
    simp only [NoCR, List.cons_append, FsSandbox.all, hx, Bool.true_and]
    exact noCRAppend xs ys hxs okY
termination_by structural xs _ _ _ => xs

private theorem digitCharToken : ∀ (n : Nat), TokenByte (byte (Char.toNat (digitChar n))) = true
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => rfl
  | _ + 9 => rfl

private theorem decCharsFuelAllToken :
    ∀ (fuel n : Nat) (acc : List Char),
      FsSandbox.all TokenByte (List.map (fun c => byte (Char.toNat c)) acc) = true →
        FsSandbox.all TokenByte
            (List.map (fun c => byte (Char.toNat c)) (decCharsFuel fuel n acc)) =
          true
  | 0, _, _, okAcc => okAcc
  | Nat.succ f, n, acc, okAcc => by
    simp only [decCharsFuel]
    split
    · simp [FsSandbox.all, digitCharToken, okAcc]
    · apply decCharsFuelAllToken f (n / 10) (digitChar (n % 10) :: acc)
      simp only [List.map, FsSandbox.all, digitCharToken, Bool.true_and, okAcc]
termination_by structural fuel _ _ _ => fuel

private theorem decCharsFuelNonEmpty :
    ∀ (fuel n : Nat) (c : Char) (cs : List Char),
      NonEmptyBytes (List.map (fun ch => byte (Char.toNat ch)) (decCharsFuel fuel n (c :: cs))) =
        true
  | 0, _, _, _ => rfl
  | Nat.succ f, n, c, cs => by
    simp only [decCharsFuel]
    split
    · rfl
    · exact decCharsFuelNonEmpty f (n / 10) (digitChar (n % 10)) (c :: cs)
termination_by structural fuel _ _ _ => fuel

private theorem decBytesValidToken (n : Nat) : ValidTokenBytes (decBytes n) = true := by
  have hne : NonEmptyBytes (decBytes n) = true := by
    simp only [decBytes, decCharsFuel]
    split
    · rfl
    · exact decCharsFuelNonEmpty n (n / 10) (digitChar (n % 10)) []
  have hat : FsSandbox.all TokenByte (decBytes n) = true :=
    decCharsFuelAllToken (Nat.succ n) n [] rfl
  simp only [ValidTokenBytes, hne, hat, Bool.true_and]

private theorem decBytesNoCR (n : Nat) : NoCR (decBytes n) = true :=
  allTokenNoCR (decBytes n) (decCharsFuelAllToken (Nat.succ n) n [] rfl)

private theorem splitCRLF :
    ∀ (acc pre rest : Bytes),
      NoCR pre = true →
        splitMarkGo (bytes "\r\n") acc (pre ++ (bytes "\r\n" ++ rest)) =
          .some (Prod.mk (List.reverse acc ++ pre) rest)
  | acc, [], rest, _ => by
    rw [List.nil_append, List.append_nil]
    rw [show bytes "\r\n" = [byte 13, byte 10] from rfl]
    rfl
  | acc, b :: bs, rest, ok => by
    have h13 : (13 == UInt8.toNat b) = false := notTrue (andLeft ok)
    have hbs : NoCR bs = true := andRight ok
    have hpfx : prefixBytes (bytes "\r\n") (b :: (bs ++ (bytes "\r\n" ++ rest))) = false := by
      rw [show bytes "\r\n" = [byte 13, byte 10] from rfl]
      have h13' : (UInt8.toNat (byte 13) == UInt8.toNat b) = false := h13
      simp only [prefixBytes, FsSandbox.prefixBytes, h13', Bool.false_and]
    simp only [List.cons_append, splitMarkGo, hpfx, Bool.false_eq_true, ite_false]
    rw [splitCRLF (b :: acc) bs rest hbs, List.reverse_cons,
      List.append_assoc (List.reverse acc) [b] bs]
    rfl
termination_by structural _ bs _ _ => bs

private theorem skipHeaderSeparator :
    ∀ (acc pre tailB : Bytes),
      NoCR pre = true →
        splitMarkGo (bytes "\r\n\r\n") acc (pre ++ tailB) =
          splitMarkGo (bytes "\r\n\r\n") (List.foldl (fun a x => x :: a) acc pre) tailB
  | _, [], _, _ => rfl
  | acc, b :: bs, tailB, ok => by
    have h13 : (13 == UInt8.toNat b) = false := notTrue (andLeft ok)
    have hbs : NoCR bs = true := andRight ok
    have hpfx : prefixBytes (bytes "\r\n\r\n") (b :: (bs ++ tailB)) = false := by
      rw [show bytes "\r\n\r\n" = [byte 13, byte 10, byte 13, byte 10] from rfl]
      have h13' : (UInt8.toNat (byte 13) == UInt8.toNat b) = false := h13
      simp only [prefixBytes, FsSandbox.prefixBytes, h13', Bool.false_and]
    simp only [List.cons_append, splitMarkGo, hpfx, Bool.false_eq_true, ite_false, List.foldl]
    exact skipHeaderSeparator (b :: acc) bs tailB hbs
termination_by structural _ bs _ _ => bs

private theorem wordsTokenStep :
    ∀ (acc tok rest : Bytes),
      FsSandbox.all TokenByte tok = true →
        wordsBytesGo acc (tok ++ byte 32 :: rest) =
          wordsBytesGo (List.foldl (fun a x => x :: a) acc tok) (byte 32 :: rest)
  | _, [], _, _ => rfl
  | acc, b :: bs, rest, ok => by
    have hsp : isAsciiSpaceByte b = false := notTrue (andLeft (andLeft ok))
    have hbs : FsSandbox.all TokenByte bs = true := andRight ok
    rw [List.cons_append, wordsBytesGo];
    simp only [hsp, Bool.false_eq_true, ite_false, List.foldl_cons]
    exact wordsTokenStep (b :: acc) bs rest hbs
termination_by structural _ xs _ _ => xs

private theorem nonEmptyFold :
    ∀ (x : Byte) (a xs : Bytes), List.foldl (fun acc y => y :: acc) (x :: a) xs ≠ []
  | _, _, [], h => nomatch h
  | _, a, y :: ys, h => nonEmptyFold y (_ :: a) ys h
termination_by structural _ _ xs => xs

private theorem wordsNonemptyToken (tok rest : Bytes) (ok : ValidTokenBytes tok = true) :
    wordsBytesGo [] (tok ++ byte 32 :: rest) = tok :: wordsBytesGo [] rest := by
  cases tok with
  | nil => cases ok
  | cons b bs =>
    have hall : FsSandbox.all TokenByte (b :: bs) = true := andRight ok
    have hsp : isAsciiSpaceByte b = false := notTrue (andLeft (andLeft hall))
    have hbs : FsSandbox.all TokenByte bs = true := andRight hall
    simp only [List.cons_append, wordsBytesGo, hsp]
    rw [wordsTokenStep [b] bs rest hbs]
    generalize hzs : List.foldl (fun a x => x :: a) [b] bs = zs
    cases zs with
    | nil => exact absurd hzs (nonEmptyFold b [] bs)
    | cons h t =>
      have hsp32 : isAsciiSpaceByte (byte 32) = true := rfl
      simp only [wordsBytesGo, hsp32, ite_true, flushWordAcc]
      congr 1
      rw [← hzs]
      simp

theorem parseHttpReqEncodeRoundtrip (method path : String) (body : Bytes)
    (okM : ValidHttpToken method = true) (okP : ValidHttpToken path = true) :
    parseHttpReq (encodeHttpReq method path [] body) =
      .some (HttpReqView.httpReqView (wireText (bytes method)) (wireText (bytes path)) body) := by
  have hm := okM
  have hp := okP
  have hmTok : FsSandbox.all TokenByte (bytes method) = true := andRight hm
  have hpTok : FsSandbox.all TokenByte (bytes path) = true := andRight hp
  let line := bytes method ++ (bytes " " ++ (bytes path ++ bytes " HTTP/1.1"))
  let hdrTail :=
    bytes "\r\nHost: 127.0.0.1\r\nConnection: close\r\nContent-Length: " ++
      (decBytes (List.length body) ++ (bytes "\r\n\r\n" ++ body))
  have noCrLine : NoCR line = true :=
    noCRAppend (bytes method) _ (allTokenNoCR _ hmTok)
      (noCRAppend (bytes " ") _ rfl
        (noCRAppend (bytes path) (bytes " HTTP/1.1") (allTokenNoCR _ hpTok) rfl))
  have reassoc : encodeHttpReq method path [] body = line ++ hdrTail := by
    simp only [encodeHttpReq, autoHeaderBytes, hasHeader, headerBytes, line, hdrTail]
    simp [List.append_assoc] <;> rfl
  have s1 :
    splitMark (bytes "\r\n") (encodeHttpReq method path [] body) =
      .some
        (Prod.mk line
          (bytes "Host: 127.0.0.1\r\nConnection: close\r\nContent-Length: " ++
            (decBytes (List.length body) ++ (bytes "\r\n\r\n" ++ body)))) := by
    rw [reassoc]
    exact splitCRLF [] line _ noCrLine
  have s2 :
    ∃ hdr,
      splitMark (bytes "\r\n\r\n") (encodeHttpReq method path [] body) = .some (Prod.mk hdr body) := by
    rw [reassoc]
    simp only [splitMark]
    rw [skipHeaderSeparator [] line hdrTail noCrLine]
    have stepLit :
      ∀ (a : Bytes),
        splitMarkGo (bytes "\r\n\r\n") a hdrTail =
          splitMarkGo (bytes "\r\n\r\n")
            (List.foldl (fun acc' x => x :: acc') a
              (bytes "\r\nHost: 127.0.0.1\r\nConnection: close\r\nContent-Length: "))
            (decBytes (List.length body) ++ (bytes "\r\n\r\n" ++ body)) :=
      fun _ => rfl
    rw [stepLit,
      skipHeaderSeparator _ (decBytes (List.length body)) (bytes "\r\n\r\n" ++ body)
        (decBytesNoCR _)]
    exact ⟨_, rfl⟩
  obtain ⟨hdr, hs2⟩ := s2
  have wLine : wordsBytes line = [bytes method, bytes path, bytes "HTTP/1.1"] := by
    simp only [wordsBytes, line]
    have hsp1 :
      bytes " " ++ (bytes path ++ bytes " HTTP/1.1") =
        byte 32 :: (bytes path ++ bytes " HTTP/1.1") :=
      rfl
    have hspH : bytes " HTTP/1.1" = byte 32 :: bytes "HTTP/1.1" := rfl
    rw [hsp1, wordsNonemptyToken (bytes method) (bytes path ++ bytes " HTTP/1.1") hm]
    rw [hspH, wordsNonemptyToken (bytes path) (bytes "HTTP/1.1") hp]
    rfl
  have hv : httpVersionBytes (bytes "HTTP/1.1") = true := rfl
  simp only [parseHttpReq, s1, hs2, wLine, requestLineBytes, hv, ite_true]

theorem parseHttpReqBodyRoundtrip (method path : String) (body : Bytes)
    (okM : ValidHttpToken method = true) (okP : ValidHttpToken path = true) :
    Option.map HttpReqView.reqBody (parseHttpReq (encodeHttpReq method path [] body)) =
      .some body :=
  congrArg (fun m => Option.map HttpReqView.reqBody m)
    (parseHttpReqEncodeRoundtrip method path body okM okP)

theorem parseHttpRespEncodeRoundtrip (status : Nat) (reason : String) (body : Bytes)
    (okStatus : statusValue (decBytes status) = .some status)
    (okReason : NoCR (bytes reason) = true) :
    parseHttpResp (encodeHttpResp status reason [] body) =
      .some (HttpRespView.httpRespView status body) := by
  have hs := okStatus
  have hr := okReason
  let line := bytes "HTTP/1.1 " ++ (decBytes status ++ (bytes " " ++ bytes reason))
  let hdrTail :=
    bytes "\r\nContent-Length: " ++
      (decBytes (List.length body) ++ (bytes "\r\nConnection: close\r\n\r\n" ++ body))
  have noCrLine : NoCR line = true :=
    noCRAppend (bytes "HTTP/1.1 ") _ rfl
      (noCRAppend (decBytes status) _ (decBytesNoCR status)
        (noCRAppend (bytes " ") (bytes reason) rfl hr))
  have reassoc : encodeHttpResp status reason [] body = line ++ hdrTail := by
    simp only [encodeHttpResp, autoHeaderBytes, hasHeader, headerBytes, line, hdrTail]
    simp [List.append_assoc] <;> rfl
  have s1 :
    splitMark (bytes "\r\n") (encodeHttpResp status reason [] body) =
      .some
        (Prod.mk line
          (bytes "Content-Length: " ++
            (decBytes (List.length body) ++ (bytes "\r\nConnection: close\r\n\r\n" ++ body)))) := by
    rw [reassoc]
    exact splitCRLF [] line _ noCrLine
  have s2 :
    ∃ hdr,
      splitMark (bytes "\r\n\r\n") (encodeHttpResp status reason [] body) =
        .some (Prod.mk hdr body) := by
    rw [reassoc]
    simp only [splitMark]
    rw [skipHeaderSeparator [] line hdrTail noCrLine]
    have stepPre :
      ∀ (a : Bytes),
        splitMarkGo (bytes "\r\n\r\n") a hdrTail =
          splitMarkGo (bytes "\r\n\r\n")
            (List.foldl (fun acc' x => x :: acc') a (bytes "\r\nContent-Length: "))
            (decBytes (List.length body) ++ (bytes "\r\nConnection: close\r\n\r\n" ++ body)) :=
      fun _ => rfl
    have stepSuf :
      ∀ (a : Bytes),
        splitMarkGo (bytes "\r\n\r\n") a (bytes "\r\nConnection: close\r\n\r\n" ++ body) =
          .some
            (Prod.mk
              (List.reverse
                (List.foldl (fun acc' x => x :: acc') a (bytes "\r\nConnection: close")))
              body) :=
      fun _ => rfl
    rw [stepPre, skipHeaderSeparator _ (decBytes (List.length body)) _ (decBytesNoCR _), stepSuf]
    exact ⟨_, rfl⟩
  obtain ⟨hdr, hs2⟩ := s2
  have wLine : wordsBytes line = bytes "HTTP/1.1" :: decBytes status :: wordsBytes (bytes reason) := by
    simp only [wordsBytes, line]
    have hpfx :
      ∀ (rest : Bytes),
        wordsBytesGo [] (bytes "HTTP/1.1 " ++ rest) = bytes "HTTP/1.1" :: wordsBytesGo [] rest :=
      fun _ => rfl
    rw [hpfx]
    have hsp : bytes " " ++ bytes reason = byte 32 :: bytes reason := rfl
    rw [hsp, wordsNonemptyToken (decBytes status) (bytes reason) (decBytesValidToken status)]
  have hv : httpVersionBytes (bytes "HTTP/1.1") = true := rfl
  simp only [parseHttpResp, s1, hs2, wLine, responseLineBytes, hv, ite_true, hs, statusView]

end LojitaCtx.NetLaws
