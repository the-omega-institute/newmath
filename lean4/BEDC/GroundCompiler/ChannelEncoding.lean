import BEDC.GroundCompiler.EventFlow

namespace BEDC.GroundCompiler.ChannelEncoding

open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow

def BodyEncoding : RawEvent -> List DisplayAlphabet
  | [] => []
  | BMark.b0 :: rest => BMark.b0 :: BodyEncoding rest
  | BMark.b1 :: rest => BMark.b1 :: BMark.b0 :: BodyEncoding rest

def EventTerminator : List DisplayAlphabet :=
  [BMark.b1, BMark.b1]

def EventEncoding (w : RawEvent) : List DisplayAlphabet :=
  BodyEncoding w ++ EventTerminator

def LegalEvent (c : List DisplayAlphabet) : Prop :=
  exists w : RawEvent, c = EventEncoding w

def FlowEncoding : EventFlow -> List DisplayAlphabet
  | [] => []
  | w :: rest => EventEncoding w ++ FlowEncoding rest

def LegalZStream (c : List DisplayAlphabet) : Prop :=
  exists S : EventFlow, c = FlowEncoding S

def DecEvent : List DisplayAlphabet -> Option (RawEvent × List DisplayAlphabet)
  | [] => none
  | BMark.b0 :: rest =>
      match DecEvent rest with
      | some (w, remaining) => some (BMark.b0 :: w, remaining)
      | none => none
  | BMark.b1 :: [] => none
  | BMark.b1 :: BMark.b0 :: rest =>
      match DecEvent rest with
      | some (w, remaining) => some (BMark.b1 :: w, remaining)
      | none => none
  | BMark.b1 :: BMark.b1 :: rest => some ([], rest)

def DecodeFuel : Nat -> List DisplayAlphabet -> Option EventFlow
  | 0, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, c =>
      match DecEvent c with
      | some (w, remaining) =>
          match DecodeFuel fuel remaining with
          | some S => some (w :: S)
          | none => none
      | none =>
          match c with
          | [] => some []
          | _ :: _ => none

def Decode (c : List DisplayAlphabet) : Option EventFlow :=
  DecodeFuel c.length c

inductive NoAdjacentOneOne : List DisplayAlphabet -> Prop where
  | nil : NoAdjacentOneOne []
  | single (m : DisplayAlphabet) : NoAdjacentOneOne [m]
  | consZero {rest : List DisplayAlphabet} :
      NoAdjacentOneOne rest -> NoAdjacentOneOne (BMark.b0 :: rest)
  | consOneZero {rest : List DisplayAlphabet} :
      NoAdjacentOneOne (BMark.b0 :: rest) ->
        NoAdjacentOneOne (BMark.b1 :: BMark.b0 :: rest)

theorem body_encoding_no_adjacent_11 (w : RawEvent) :
    NoAdjacentOneOne (BodyEncoding w) := by
  induction w with
  | nil =>
      exact NoAdjacentOneOne.nil
  | cons m rest ih =>
      cases m with
      | b0 =>
          exact NoAdjacentOneOne.consZero ih
      | b1 =>
          exact NoAdjacentOneOne.consOneZero
            (NoAdjacentOneOne.consZero ih)

theorem first_11_is_terminator (w : RawEvent) :
    NoAdjacentOneOne (BodyEncoding w) /\
      EventEncoding w = BodyEncoding w ++ EventTerminator := by
  constructor
  · exact body_encoding_no_adjacent_11 w
  · rfl

theorem flow_encoding_legal_zstream (S : EventFlow) :
    LegalZStream (FlowEncoding S) := by
  exact ⟨S, rfl⟩

theorem flow_encoding_not_single_one (S : EventFlow) :
    Not (FlowEncoding S = [BMark.b1]) := by
  intro h
  cases S with
  | nil =>
      cases h
  | cons w rest =>
      cases w with
      | nil =>
          simp [FlowEncoding, EventEncoding, BodyEncoding, EventTerminator] at h
      | cons m tail =>
          cases m <;>
            simp [FlowEncoding, EventEncoding, BodyEncoding, EventTerminator] at h

theorem channel_encoding_0111_illegal :
    Not (LegalZStream [BMark.b0, BMark.b1, BMark.b1, BMark.b1]) := by
  intro h
  cases h with
  | intro S hS =>
      cases S with
      | nil =>
          cases hS
      | cons w rest =>
          cases w with
          | nil =>
              simp [FlowEncoding, EventEncoding, BodyEncoding, EventTerminator] at hS
          | cons m tail =>
              cases m with
              | b0 =>
                  cases tail with
                  | nil =>
                      have hrest : [BMark.b1] = FlowEncoding rest := by
                        simpa [FlowEncoding, EventEncoding, BodyEncoding,
                          EventTerminator] using hS
                      exact flow_encoding_not_single_one rest hrest.symm
                  | cons n tailRest =>
                      cases n <;>
                        simp [FlowEncoding, EventEncoding, BodyEncoding,
                          EventTerminator] at hS
              | b1 =>
                  simp [FlowEncoding, EventEncoding, BodyEncoding, EventTerminator] at hS

theorem event_level_round_trip (w : RawEvent) :
    DecEvent (EventEncoding w) = some (w, []) := by
  induction w with
  | nil =>
      rfl
  | cons m rest ih =>
      cases m with
      | b0 =>
          have h :
              DecEvent (BodyEncoding rest ++ EventTerminator) =
                some (rest, []) := by
            simpa [EventEncoding] using ih
          simp [EventEncoding, BodyEncoding, DecEvent, h]
      | b1 =>
          have h :
              DecEvent (BodyEncoding rest ++ EventTerminator) =
                some (rest, []) := by
            simpa [EventEncoding] using ih
          simp [EventEncoding, BodyEncoding, DecEvent, h]

theorem dec_event_append_event_encoding
    (w : RawEvent) (restCode : List DisplayAlphabet) :
    DecEvent (EventEncoding w ++ restCode) = some (w, restCode) := by
  induction w with
  | nil =>
      rfl
  | cons m rest ih =>
      cases m with
      | b0 =>
          have h :
              DecEvent (BodyEncoding rest ++ (EventTerminator ++ restCode)) =
                some (rest, restCode) := by
            simpa [EventEncoding, List.append_assoc] using ih
          simp [EventEncoding, BodyEncoding, DecEvent, h]
      | b1 =>
          have h :
              DecEvent (BodyEncoding rest ++ (EventTerminator ++ restCode)) =
                some (rest, restCode) := by
            simpa [EventEncoding, List.append_assoc] using ih
          simp [EventEncoding, BodyEncoding, DecEvent, h]

theorem decode_fuel_flow_encoding (S : EventFlow) (extra : Nat) :
    DecodeFuel (S.length + extra) (FlowEncoding S) = some S := by
  induction S with
  | nil =>
      cases extra <;> rfl
  | cons w rest ih =>
      change
        DecodeFuel ((w :: rest).length + extra)
          (EventEncoding w ++ FlowEncoding rest) = some (w :: rest)
      have hFuel :
          (w :: rest).length + extra = (rest.length + extra) + 1 := by
        simp [Nat.add_assoc, Nat.add_comm]
      rw [hFuel]
      simp [DecodeFuel, dec_event_append_event_encoding, ih]

theorem flow_encoding_length_has_event_fuel (S : EventFlow) :
    exists extra : Nat, (FlowEncoding S).length = S.length + extra := by
  induction S with
  | nil =>
      exact ⟨0, rfl⟩
  | cons w rest ih =>
      cases ih with
      | intro extra hrest =>
          refine ⟨(BodyEncoding w).length + 1 + extra, ?_⟩
          simp [FlowEncoding, EventEncoding, EventTerminator, hrest,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          have htwo (n : Nat) : 2 + n = 1 + (1 + n) := by
            rw [show 2 = 1 + 1 by rfl, Nat.add_assoc]
          exact htwo (BodyEncoding w).length

theorem flow_level_round_trip (S : EventFlow) :
    Decode (FlowEncoding S) = some S := by
  cases flow_encoding_length_has_event_fuel S with
  | intro extra hlen =>
      rw [Decode, hlen]
      exact decode_fuel_flow_encoding S extra

theorem encoder_streaming (w : RawEvent) (rest : EventFlow) :
    FlowEncoding (w :: rest) = EventEncoding w ++ FlowEncoding rest := by
  rfl

theorem decoder_streaming_one_glyph_lookahead :
    DecEvent [] = none /\
      (forall rest : List DisplayAlphabet,
        DecEvent (BMark.b0 :: rest) =
          match DecEvent rest with
          | some (w, remaining) => some (BMark.b0 :: w, remaining)
          | none => none) /\
      DecEvent [BMark.b1] = none /\
      (forall rest : List DisplayAlphabet,
        DecEvent (BMark.b1 :: BMark.b0 :: rest) =
          match DecEvent rest with
          | some (w, remaining) => some (BMark.b1 :: w, remaining)
          | none => none) /\
      (forall rest : List DisplayAlphabet,
        DecEvent (BMark.b1 :: BMark.b1 :: rest) = some ([], rest)) := by
  constructor
  · rfl
  · constructor
    · intro rest
      rfl
    · constructor
      · rfl
      · constructor
        · intro rest
          rfl
        · intro rest
          rfl

theorem no_tree_no_manifest_no_table {d : CompilerDatum} :
    StructuralHiddenInput d -> Not (FormalCompilerInput d) := by
  exact structural_hidden_not_formal

theorem flow_encoding_eq_nil {S : EventFlow} :
    FlowEncoding S = [] -> S = [] := by
  intro h
  cases S with
  | nil =>
      rfl
  | cons w rest =>
      cases w with
      | nil =>
          simp [FlowEncoding, EventEncoding, BodyEncoding, EventTerminator] at h
      | cons m tail =>
          cases m <;>
            simp [FlowEncoding, EventEncoding, BodyEncoding, EventTerminator] at h

theorem legal_stream_not_theoremhood :
    exists c : List DisplayAlphabet,
      LegalZStream c /\
        Not (exists S : EventFlow,
          c = FlowEncoding S /\ RecognizedTheoremFlow S) := by
  refine ⟨[], ?_, ?_⟩
  · exact ⟨[], rfl⟩
  · intro h
    cases h with
    | intro S hS =>
        cases hS with
        | intro hEq hTheo =>
            have hNil : S = [] := flow_encoding_eq_nil hEq.symm
            cases hNil
            exact empty_not_recognized_theorem_flow hTheo

theorem legal_stream_completeness {c : List DisplayAlphabet} :
    LegalZStream c ->
      exists S : EventFlow, Decode c = some S /\ FlowEncoding S = c := by
  intro h
  cases h with
  | intro S hS =>
      exact ⟨S, by rw [hS]; exact flow_level_round_trip S, hS.symm⟩

theorem channel_encoding_bijection :
    (forall S : EventFlow, Decode (FlowEncoding S) = some S) /\
      (forall c : List DisplayAlphabet,
        LegalZStream c ->
          exists S : EventFlow, Decode c = some S /\ FlowEncoding S = c) := by
  constructor
  · intro S
    exact flow_level_round_trip S
  · intro c h
    exact legal_stream_completeness h

theorem channel_conservativity {S : EventFlow} {m : DisplayAlphabet} :
    List.Mem m (FlowEncoding S) -> m = BMark.b0 \/ m = BMark.b1 := by
  intro _
  cases m with
  | b0 => exact Or.inl rfl
  | b1 => exact Or.inr rfl

end BEDC.GroundCompiler.ChannelEncoding
