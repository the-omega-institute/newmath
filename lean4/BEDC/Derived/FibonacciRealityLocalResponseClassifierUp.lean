namespace BEDC.Derived.FibonacciRealityLocalResponseClassifierUp

inductive Bit : Type where
  | z
  | o
  deriving DecidableEq

inductive HistLE3 : Type where
  | empty
  | one (a : Bit)
  | two (a b : Bit)
  | three (a b c : Bit)
  deriving DecidableEq

inductive HistLE4 : Type where
  | empty
  | one (a : Bit)
  | two (a b : Bit)
  | three (a b c : Bit)
  | four (a b c d : Bit)
  deriving DecidableEq

inductive Response : Type where
  | Gap
  | ZeroResp
  | NonzeroResp
  deriving DecidableEq

def embed : HistLE3 -> HistLE4
  | HistLE3.empty => HistLE4.empty
  | HistLE3.one a => HistLE4.one a
  | HistLE3.two a b => HistLE4.two a b
  | HistLE3.three a b c => HistLE4.three a b c

def cont : HistLE3 -> Bit -> HistLE4
  | HistLE3.empty, d => HistLE4.one d
  | HistLE3.one a, d => HistLE4.two a d
  | HistLE3.two a b, d => HistLE4.three a b d
  | HistLE3.three a b c, d => HistLE4.four a b c d

def terminal3 : HistLE3 -> Option Bit
  | HistLE3.empty => none
  | HistLE3.one a => some a
  | HistLE3.two _ b => some b
  | HistLE3.three _ _ c => some c

def terminal4 : HistLE4 -> Option Bit
  | HistLE4.empty => none
  | HistLE4.one a => some a
  | HistLE4.two _ b => some b
  | HistLE4.three _ _ c => some c
  | HistLE4.four _ _ _ d => some d

def bitResponse : Bit -> Bit -> Response
  | Bit.z, Bit.z => Response.ZeroResp
  | Bit.z, Bit.o => Response.NonzeroResp
  | Bit.o, Bit.z => Response.NonzeroResp
  | Bit.o, Bit.o => Response.ZeroResp

def optionBitResponse : Option Bit -> Option Bit -> Response
  | none, _ => Response.Gap
  | some _, none => Response.Gap
  | some a, some b => bitResponse a b

def classifyTerminal (h : HistLE3) (d : Bit) : Response :=
  optionBitResponse (terminal3 h) (terminal4 (cont h d))

def classifyFullWord (_h : HistLE3) (_d : Bit) : Response :=
  Response.NonzeroResp

theorem terminal_empty_continuations_are_gaps :
    classifyTerminal HistLE3.empty Bit.z = Response.Gap ∧
      classifyTerminal HistLE3.empty Bit.o = Response.Gap := by
  exact ⟨rfl, rfl⟩

theorem terminal_same_bit_is_zero_response :
    classifyTerminal (HistLE3.one Bit.z) Bit.z = Response.ZeroResp ∧
      classifyTerminal (HistLE3.one Bit.o) Bit.o = Response.ZeroResp := by
  exact ⟨rfl, rfl⟩

theorem terminal_changed_bit_is_nonzero_response :
    classifyTerminal (HistLE3.one Bit.z) Bit.o = Response.NonzeroResp ∧
      classifyTerminal (HistLE3.one Bit.o) Bit.z = Response.NonzeroResp := by
  exact ⟨rfl, rfl⟩

theorem full_word_one_step_is_nonzero :
    forall h : HistLE3,
      forall d : Bit,
        classifyFullWord h d = Response.NonzeroResp := by
  intro h d
  rfl

theorem zero_response_does_not_mean_raw_identity :
    classifyTerminal (HistLE3.one Bit.o) Bit.o = Response.ZeroResp ∧
      cont (HistLE3.one Bit.o) Bit.o ≠ embed (HistLE3.one Bit.o) := by
  constructor
  · rfl
  · intro same
    cases same

theorem terminal_zero_and_full_word_nonzero_can_coexist :
    classifyTerminal (HistLE3.one Bit.z) Bit.z = Response.ZeroResp ∧
      classifyFullWord (HistLE3.one Bit.z) Bit.z = Response.NonzeroResp := by
  exact ⟨rfl, rfl⟩

theorem local_response_classifier_certificate :
    (classifyTerminal HistLE3.empty Bit.z = Response.Gap ∧
        classifyTerminal HistLE3.empty Bit.o = Response.Gap) ∧
      (classifyTerminal (HistLE3.one Bit.z) Bit.z = Response.ZeroResp ∧
        classifyTerminal (HistLE3.one Bit.o) Bit.o = Response.ZeroResp) ∧
        (classifyTerminal (HistLE3.one Bit.z) Bit.o = Response.NonzeroResp ∧
          classifyTerminal (HistLE3.one Bit.o) Bit.z = Response.NonzeroResp) ∧
          (forall h : HistLE3,
            forall d : Bit,
              classifyFullWord h d = Response.NonzeroResp) ∧
            (classifyTerminal (HistLE3.one Bit.o) Bit.o = Response.ZeroResp ∧
              cont (HistLE3.one Bit.o) Bit.o ≠ embed (HistLE3.one Bit.o)) ∧
              (classifyTerminal (HistLE3.one Bit.z) Bit.z = Response.ZeroResp ∧
                classifyFullWord (HistLE3.one Bit.z) Bit.z =
                  Response.NonzeroResp) := by
  exact
    ⟨terminal_empty_continuations_are_gaps,
      terminal_same_bit_is_zero_response,
      terminal_changed_bit_is_nonzero_response,
      full_word_one_step_is_nonzero,
      zero_response_does_not_mean_raw_identity,
      terminal_zero_and_full_word_nonzero_can_coexist⟩

end BEDC.Derived.FibonacciRealityLocalResponseClassifierUp
