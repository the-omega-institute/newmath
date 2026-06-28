import BEDC.Derived.RealIntervalUp.TasteGate

namespace BEDC.Derived.RealIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealIntervalFiniteEndpointEnvelopeRoute [AskSetup] [PackageSetup]
    {D W R E S H C N envelopeRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory D -> UnaryHistory W -> UnaryHistory E -> UnaryHistory H ->
      UnaryHistory N -> Cont D W R -> Cont R E S -> Cont S H C ->
        Cont C N envelopeRead -> PkgSig bundle N pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row envelopeRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row D ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
                  hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row N ∨
                    hsame row envelopeRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont D W R ∧ Cont R E S ∧ Cont S H C ∧
                  Cont C N envelopeRead ∧ PkgSig bundle N pkg)
              hsame ∧
            UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory C ∧
              UnaryHistory envelopeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro unaryD unaryW unaryE unaryH unaryN dyadicRead enclosureRead replayRead
    envelopeRoute pkgN
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryD unaryW dyadicRead
  have unaryS : UnaryHistory S :=
    unary_cont_closed unaryR unaryE enclosureRead
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryS unaryH replayRead
  have unaryEnvelope : UnaryHistory envelopeRead :=
    unary_cont_closed unaryC unaryN envelopeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row envelopeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
              hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row N ∨
                hsame row envelopeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D W R ∧ Cont R E S ∧ Cont S H C ∧
              Cont C N envelopeRead ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro envelopeRead ⟨hsame_refl envelopeRead, unaryEnvelope⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, dyadicRead, enclosureRead, replayRead, envelopeRoute, pkgN⟩
  }
  exact ⟨cert, unaryR, unaryS, unaryC, unaryEnvelope⟩

end BEDC.Derived.RealIntervalUp
