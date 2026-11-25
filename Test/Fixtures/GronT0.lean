namespace Gen.T0.Gron
inductive Source where
  | stdin
  | file
  | http
deriving DecidableEq
inductive Framing where
  | document
  | lines
deriving DecidableEq
inductive Wire where
  | assignments
  | jsonRows
deriving DecidableEq
inductive ForwardResult where
  | complete
  | malformed
  | readError
deriving DecidableEq
inductive ValuesResult where
  | quiet
  | emitted
  | malformed (stdoutEmitted : Bool)
  | panic (stdoutEmitted : Bool)
deriving DecidableEq
inductive ReverseResult where
  | complete
  | noStatements
  | malformed
  | conflictingPaths
  | readError
  | negativeIndex
  | encodeError
deriving DecidableEq
inductive Invocation where
  | help
  | version
  | badFlags
  | openError
  | fetchError
  | forward (source : Source) (framing : Framing) (wire : Wire) (result : ForwardResult)
  | values (result : ValuesResult)
  | reverse (source : Source) (wire : Wire) (result : ReverseResult)
deriving DecidableEq
structure Observation where
  status : Nat
  stdoutEmitted : Bool
  stderrEmitted : Bool
deriving DecidableEq
def observe : Invocation → Observation
  | .help => ⟨0, false, true⟩
  | .version => ⟨0, true, false⟩
  | .badFlags => ⟨2, false, true⟩
  | .openError => ⟨1, false, true⟩
  | .fetchError => ⟨4, false, true⟩
  | .forward _ framing _ result =>
      match result with
      | .complete => ⟨0, true, false⟩
      | .malformed | .readError =>
          match framing with
          | .document => ⟨3, false, true⟩
          | .lines => ⟨3, true, true⟩
  | .values result =>
      match result with
      | .quiet => ⟨0, false, false⟩
      | .emitted => ⟨0, true, false⟩
      | .malformed emitted => ⟨5, emitted, true⟩
      | .panic emitted => ⟨2, emitted, true⟩
  | .reverse _ _ result =>
      match result with
      | .complete => ⟨0, true, false⟩
      | .noStatements | .malformed | .conflictingPaths => ⟨5, false, true⟩
      | .readError | .negativeIndex => ⟨2, false, true⟩
      | .encodeError => ⟨6, false, true⟩
theorem helpObservation :
  observe .help = ⟨0, false, true⟩ := rfl
theorem versionObservation :
  observe .version = ⟨0, true, false⟩ := rfl
theorem flagErrorObservation :
  observe .badFlags = ⟨2, false, true⟩ := rfl
theorem openErrorObservation :
  observe .openError = ⟨1, false, true⟩ := rfl
theorem fetchErrorObservation :
  observe .fetchError = ⟨4, false, true⟩ := rfl
theorem valuesQuiet :
  observe (.values .quiet) = ⟨0, false, false⟩ := rfl
theorem valuesEmitted :
  observe (.values .emitted) = ⟨0, true, false⟩ := rfl
theorem valuesMalformed :
  ∀ emitted, observe (.values (.malformed emitted)) = ⟨5, emitted, true⟩ :=
  fun _ => rfl
theorem valuesPanic :
  ∀ emitted, observe (.values (.panic emitted)) = ⟨2, emitted, true⟩ :=
  fun _ => rfl
theorem forwardComplete :
  ∀ source framing wire,
    observe (.forward source framing wire .complete) = ⟨0, true, false⟩ :=
  fun _ _ _ => rfl
theorem documentMalformed :
  ∀ source wire,
    observe (.forward source .document wire .malformed) = ⟨3, false, true⟩ :=
  fun _ _ => rfl
theorem lineMalformed :
  ∀ source wire,
    observe (.forward source .lines wire .malformed) = ⟨3, true, true⟩ :=
  fun _ _ => rfl
theorem documentReadError :
  ∀ source wire,
    observe (.forward source .document wire .readError) = ⟨3, false, true⟩ :=
  fun _ _ => rfl
theorem lineReadError :
  ∀ source wire,
    observe (.forward source .lines wire .readError) = ⟨3, true, true⟩ :=
  fun _ _ => rfl
theorem reverseComplete :
  ∀ source wire,
    observe (.reverse source wire .complete) = ⟨0, true, false⟩ :=
  fun _ _ => rfl
theorem reverseEmpty :
  ∀ source wire,
    observe (.reverse source wire .noStatements) = ⟨5, false, true⟩ :=
  fun _ _ => rfl
theorem reverseMalformed :
  ∀ source wire,
    observe (.reverse source wire .malformed) = ⟨5, false, true⟩ :=
  fun _ _ => rfl
theorem reverseConflict :
  ∀ source wire,
    observe (.reverse source wire .conflictingPaths) = ⟨5, false, true⟩ :=
  fun _ _ => rfl
theorem reverseReadError :
  ∀ source wire,
    observe (.reverse source wire .readError) = ⟨2, false, true⟩ :=
  fun _ _ => rfl
theorem reverseNegativeIndex :
  ∀ source wire,
    observe (.reverse source wire .negativeIndex) = ⟨2, false, true⟩ :=
  fun _ _ => rfl
theorem reverseEncodeError :
  ∀ source wire,
    (observe (.reverse source wire .encodeError)).status = 6 :=
  fun _ _ => rfl
end Gen.T0.Gron
