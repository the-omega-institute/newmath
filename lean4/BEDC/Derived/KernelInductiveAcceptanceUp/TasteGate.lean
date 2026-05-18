import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KernelInductiveAcceptanceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KernelInductiveAcceptanceUp : Type where
  | mk :
      (declaration signatures eliminators positivity recursion transport routes provenance
        nameCert : BHist) →
      KernelInductiveAcceptanceUp
  deriving DecidableEq

def kernelInductiveAcceptanceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kernelInductiveAcceptanceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kernelInductiveAcceptanceEncodeBHist h

def kernelInductiveAcceptanceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kernelInductiveAcceptanceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kernelInductiveAcceptanceDecodeBHist tail)

private theorem kernelInductiveAcceptanceDecode_encode_bhist :
    ∀ h : BHist,
      kernelInductiveAcceptanceDecodeBHist
        (kernelInductiveAcceptanceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def kernelInductiveAcceptanceToEventFlow :
    KernelInductiveAcceptanceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | KernelInductiveAcceptanceUp.mk declaration signatures eliminators positivity recursion
      transport routes provenance nameCert =>
      [[BMark.b0],
        kernelInductiveAcceptanceEncodeBHist declaration,
        [BMark.b1, BMark.b0],
        kernelInductiveAcceptanceEncodeBHist signatures,
        [BMark.b1, BMark.b1, BMark.b0],
        kernelInductiveAcceptanceEncodeBHist eliminators,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelInductiveAcceptanceEncodeBHist positivity,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelInductiveAcceptanceEncodeBHist recursion,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelInductiveAcceptanceEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelInductiveAcceptanceEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        kernelInductiveAcceptanceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        kernelInductiveAcceptanceEncodeBHist nameCert]

def kernelInductiveAcceptanceFromEventFlow :
    EventFlow → Option KernelInductiveAcceptanceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | declaration :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | signatures :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | eliminators :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | positivity :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | recursion :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | routes :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | nameCert :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (KernelInductiveAcceptanceUp.mk
                                                                                  (kernelInductiveAcceptanceDecodeBHist
                                                                                    declaration)
                                                                                  (kernelInductiveAcceptanceDecodeBHist
                                                                                    signatures)
                                                                                  (kernelInductiveAcceptanceDecodeBHist
                                                                                    eliminators)
                                                                                  (kernelInductiveAcceptanceDecodeBHist
                                                                                    positivity)
                                                                                  (kernelInductiveAcceptanceDecodeBHist
                                                                                    recursion)
                                                                                  (kernelInductiveAcceptanceDecodeBHist
                                                                                    transport)
                                                                                  (kernelInductiveAcceptanceDecodeBHist
                                                                                    routes)
                                                                                  (kernelInductiveAcceptanceDecodeBHist
                                                                                    provenance)
                                                                                  (kernelInductiveAcceptanceDecodeBHist
                                                                                    nameCert))
                                                                          | _ :: _ => none

private theorem kernelInductiveAcceptance_round_trip :
    ∀ x : KernelInductiveAcceptanceUp,
      kernelInductiveAcceptanceFromEventFlow
        (kernelInductiveAcceptanceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk declaration signatures eliminators positivity recursion transport routes provenance
      nameCert =>
      change
        some
          (KernelInductiveAcceptanceUp.mk
            (kernelInductiveAcceptanceDecodeBHist
              (kernelInductiveAcceptanceEncodeBHist declaration))
            (kernelInductiveAcceptanceDecodeBHist
              (kernelInductiveAcceptanceEncodeBHist signatures))
            (kernelInductiveAcceptanceDecodeBHist
              (kernelInductiveAcceptanceEncodeBHist eliminators))
            (kernelInductiveAcceptanceDecodeBHist
              (kernelInductiveAcceptanceEncodeBHist positivity))
            (kernelInductiveAcceptanceDecodeBHist
              (kernelInductiveAcceptanceEncodeBHist recursion))
            (kernelInductiveAcceptanceDecodeBHist
              (kernelInductiveAcceptanceEncodeBHist transport))
            (kernelInductiveAcceptanceDecodeBHist
              (kernelInductiveAcceptanceEncodeBHist routes))
            (kernelInductiveAcceptanceDecodeBHist
              (kernelInductiveAcceptanceEncodeBHist provenance))
            (kernelInductiveAcceptanceDecodeBHist
              (kernelInductiveAcceptanceEncodeBHist nameCert))) =
          some
            (KernelInductiveAcceptanceUp.mk declaration signatures eliminators positivity
              recursion transport routes provenance nameCert)
      rw [kernelInductiveAcceptanceDecode_encode_bhist declaration,
        kernelInductiveAcceptanceDecode_encode_bhist signatures,
        kernelInductiveAcceptanceDecode_encode_bhist eliminators,
        kernelInductiveAcceptanceDecode_encode_bhist positivity,
        kernelInductiveAcceptanceDecode_encode_bhist recursion,
        kernelInductiveAcceptanceDecode_encode_bhist transport,
        kernelInductiveAcceptanceDecode_encode_bhist routes,
        kernelInductiveAcceptanceDecode_encode_bhist provenance,
        kernelInductiveAcceptanceDecode_encode_bhist nameCert]

private theorem kernelInductiveAcceptanceToEventFlow_injective
    {x y : KernelInductiveAcceptanceUp} :
    kernelInductiveAcceptanceToEventFlow x =
      kernelInductiveAcceptanceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kernelInductiveAcceptanceFromEventFlow
          (kernelInductiveAcceptanceToEventFlow x) =
        kernelInductiveAcceptanceFromEventFlow
          (kernelInductiveAcceptanceToEventFlow y) :=
    congrArg kernelInductiveAcceptanceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (kernelInductiveAcceptance_round_trip x).symm
      (Eq.trans hread (kernelInductiveAcceptance_round_trip y)))

instance kernelInductiveAcceptanceBHistCarrier :
    BHistCarrier KernelInductiveAcceptanceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kernelInductiveAcceptanceToEventFlow
  fromEventFlow := kernelInductiveAcceptanceFromEventFlow

instance kernelInductiveAcceptanceChapterTasteGate :
    ChapterTasteGate KernelInductiveAcceptanceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      kernelInductiveAcceptanceFromEventFlow
        (kernelInductiveAcceptanceToEventFlow x) = some x
    exact kernelInductiveAcceptance_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (kernelInductiveAcceptanceToEventFlow_injective heq)

instance kernelInductiveAcceptanceFieldFaithful :
    FieldFaithful KernelInductiveAcceptanceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | KernelInductiveAcceptanceUp.mk declaration signatures eliminators positivity recursion
        transport routes provenance nameCert =>
        [declaration, signatures, eliminators, positivity, recursion, transport, routes,
          provenance, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk declaration₁ signatures₁ eliminators₁ positivity₁ recursion₁ transport₁ routes₁
        provenance₁ nameCert₁ =>
        cases y with
        | mk declaration₂ signatures₂ eliminators₂ positivity₂ recursion₂ transport₂ routes₂
            provenance₂ nameCert₂ =>
            simp only [] at h
            cases h
            rfl

def taste_gate : ChapterTasteGate KernelInductiveAcceptanceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kernelInductiveAcceptanceChapterTasteGate

theorem KernelInductiveAcceptanceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      kernelInductiveAcceptanceDecodeBHist
        (kernelInductiveAcceptanceEncodeBHist h) = h) ∧
      (∀ x : KernelInductiveAcceptanceUp,
        kernelInductiveAcceptanceFromEventFlow
          (kernelInductiveAcceptanceToEventFlow x) = some x) ∧
        (∀ x y : KernelInductiveAcceptanceUp,
          kernelInductiveAcceptanceToEventFlow x =
            kernelInductiveAcceptanceToEventFlow y → x = y) ∧
          kernelInductiveAcceptanceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact kernelInductiveAcceptanceDecode_encode_bhist
  · constructor
    · exact kernelInductiveAcceptance_round_trip
    · constructor
      · intro x y heq
        exact kernelInductiveAcceptanceToEventFlow_injective heq
      · rfl

theorem KernelInductiveAcceptanceUp_constructor_ledger_exhaustion
    [AskSetup] [PackageSetup]
    {declaration signatures eliminators positivity recursion transport routes provenance
      nameCert constructorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont declaration signatures constructorRead →
      Cont constructorRead routes provenance →
        PkgSig bundle provenance pkg →
          UnaryHistory declaration →
            UnaryHistory signatures →
              UnaryHistory routes →
                UnaryHistory constructorRead ∧ Cont declaration signatures constructorRead ∧
                  Cont constructorRead routes provenance ∧ PkgSig bundle provenance pkg ∧
                    List.Mem (kernelInductiveAcceptanceEncodeBHist signatures)
                      (kernelInductiveAcceptanceToEventFlow
                        (KernelInductiveAcceptanceUp.mk declaration signatures eliminators
                          positivity recursion transport routes provenance nameCert)) := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle Pkg
  intro declarationSignaturesConstructor constructorRoutesProvenance provenancePkg
    _declarationUnary _signaturesUnary routesUnary
  have constructorUnary : UnaryHistory constructorRead :=
    unary_cont_closed _declarationUnary _signaturesUnary declarationSignaturesConstructor
  have signaturesListed :
      List.Mem (kernelInductiveAcceptanceEncodeBHist signatures)
        (kernelInductiveAcceptanceToEventFlow
          (KernelInductiveAcceptanceUp.mk declaration signatures eliminators positivity recursion
            transport routes provenance nameCert)) := by
    change
      List.Mem (kernelInductiveAcceptanceEncodeBHist signatures)
        [[BMark.b0], kernelInductiveAcceptanceEncodeBHist declaration, [BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist signatures, [BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist eliminators,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist positivity,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist recursion,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist transport,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist routes,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          kernelInductiveAcceptanceEncodeBHist provenance,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist nameCert]
    exact
      List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self))
  exact
    ⟨constructorUnary, declarationSignaturesConstructor, constructorRoutesProvenance,
      provenancePkg, signaturesListed⟩

theorem KernelInductiveAcceptanceUp_eliminator_ledger_exhaustion
    [AskSetup] [PackageSetup]
    {declaration signatures eliminators positivity recursion transport routes provenance
      nameCert eliminatorRead recursorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont signatures eliminators eliminatorRead →
      Cont eliminatorRead recursion recursorRead →
        PkgSig bundle recursorRead pkg →
          UnaryHistory signatures →
            UnaryHistory eliminators →
              UnaryHistory recursion →
                UnaryHistory eliminatorRead ∧ UnaryHistory recursorRead ∧
                  Cont signatures eliminators eliminatorRead ∧
                    Cont eliminatorRead recursion recursorRead ∧
                      PkgSig bundle recursorRead pkg ∧
                        List.Mem (kernelInductiveAcceptanceEncodeBHist eliminators)
                          (kernelInductiveAcceptanceToEventFlow
                            (KernelInductiveAcceptanceUp.mk declaration signatures eliminators
                              positivity recursion transport routes provenance nameCert)) ∧
                          List.Mem (kernelInductiveAcceptanceEncodeBHist recursion)
                            (kernelInductiveAcceptanceToEventFlow
                              (KernelInductiveAcceptanceUp.mk declaration signatures eliminators
                                positivity recursion transport routes provenance nameCert)) := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle Pkg
  intro signaturesEliminatorsRead eliminatorRecursionRead recursorPkg signaturesUnary
    eliminatorsUnary recursionUnary
  have eliminatorUnary : UnaryHistory eliminatorRead :=
    unary_cont_closed signaturesUnary eliminatorsUnary signaturesEliminatorsRead
  have recursorUnary : UnaryHistory recursorRead :=
    unary_cont_closed eliminatorUnary recursionUnary eliminatorRecursionRead
  have eliminatorsListed :
      List.Mem (kernelInductiveAcceptanceEncodeBHist eliminators)
        (kernelInductiveAcceptanceToEventFlow
          (KernelInductiveAcceptanceUp.mk declaration signatures eliminators positivity recursion
            transport routes provenance nameCert)) := by
    change
      List.Mem (kernelInductiveAcceptanceEncodeBHist eliminators)
        [[BMark.b0], kernelInductiveAcceptanceEncodeBHist declaration, [BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist signatures, [BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist eliminators,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist positivity,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist recursion,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist transport,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist routes,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          kernelInductiveAcceptanceEncodeBHist provenance,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist nameCert]
    exact
      List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ List.mem_cons_self))))
  have recursionListed :
      List.Mem (kernelInductiveAcceptanceEncodeBHist recursion)
        (kernelInductiveAcceptanceToEventFlow
          (KernelInductiveAcceptanceUp.mk declaration signatures eliminators positivity recursion
            transport routes provenance nameCert)) := by
    change
      List.Mem (kernelInductiveAcceptanceEncodeBHist recursion)
        [[BMark.b0], kernelInductiveAcceptanceEncodeBHist declaration, [BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist signatures, [BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist eliminators,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist positivity,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist recursion,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist transport,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist routes,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          kernelInductiveAcceptanceEncodeBHist provenance,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist nameCert]
    exact
      List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _
                      (List.mem_cons_of_mem _ List.mem_cons_self))))))))
  exact
    ⟨eliminatorUnary, recursorUnary, signaturesEliminatorsRead, eliminatorRecursionRead,
      recursorPkg, eliminatorsListed, recursionListed⟩

theorem KernelInductiveAcceptanceUp_accepted_declaration_route
    [AskSetup] [PackageSetup]
    {declaration signatures eliminators positivity recursion transport routes provenance
      nameCert entry : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont declaration signatures eliminators ->
      Cont eliminators recursion entry ->
        PkgSig bundle entry pkg ->
          UnaryHistory declaration ->
            UnaryHistory signatures ->
              UnaryHistory eliminators ->
                UnaryHistory recursion ->
                  UnaryHistory declaration ∧ UnaryHistory signatures ∧
                    UnaryHistory eliminators ∧ UnaryHistory recursion ∧ UnaryHistory entry ∧
                      Cont declaration signatures eliminators ∧
                        Cont eliminators recursion entry ∧ PkgSig bundle entry pkg ∧
                          List.Mem (kernelInductiveAcceptanceEncodeBHist declaration)
                            (kernelInductiveAcceptanceToEventFlow
                              (KernelInductiveAcceptanceUp.mk declaration signatures eliminators
                                positivity recursion transport routes provenance nameCert)) := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle Pkg
  intro declarationSignaturesEliminators eliminatorsRecursionEntry entryPkg declarationUnary
    signaturesUnary eliminatorsUnary recursionUnary
  have entryUnary : UnaryHistory entry :=
    unary_cont_closed eliminatorsUnary recursionUnary eliminatorsRecursionEntry
  have declarationListed :
      List.Mem (kernelInductiveAcceptanceEncodeBHist declaration)
        (kernelInductiveAcceptanceToEventFlow
          (KernelInductiveAcceptanceUp.mk declaration signatures eliminators positivity recursion
            transport routes provenance nameCert)) := by
    change
      List.Mem (kernelInductiveAcceptanceEncodeBHist declaration)
        [[BMark.b0], kernelInductiveAcceptanceEncodeBHist declaration, [BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist signatures, [BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist eliminators,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist positivity,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist recursion,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist transport,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist routes,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          kernelInductiveAcceptanceEncodeBHist provenance,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist nameCert]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  exact
    ⟨declarationUnary, signaturesUnary, eliminatorsUnary, recursionUnary, entryUnary,
      declarationSignaturesEliminators, eliminatorsRecursionEntry, entryPkg,
      declarationListed⟩

end BEDC.Derived.KernelInductiveAcceptanceUp
