import BEDC.Derived.FiniteHistLocalityPacketUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.FiniteHistLocalityPacketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteHistLocalityPacketKernelCarrier [AskSetup] [PackageSetup]
    (H0 H1 L I S T C Q N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory H0 ∧ UnaryHistory H1 ∧ UnaryHistory I ∧ UnaryHistory T ∧
    UnaryHistory N ∧ Cont H0 H1 L ∧ Cont L I S ∧ Cont S T C ∧
      PkgSig bundle Q pkg ∧ PkgSig bundle N pkg

theorem FiniteHistLocalityPacketScopedKernelScope [AskSetup] [PackageSetup]
    {H0 H1 L I S T C Q N consumerRead : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    FiniteHistLocalityPacketKernelCarrier H0 H1 L I S T C Q N bundle pkg ->
      Cont C N consumerRead -> PkgSig bundle consumerRead pkg ->
        SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row H0 ∨ hsame row H1 ∨ hsame row L ∨ hsame row I ∨
              hsame row S ∨ hsame row T ∨ hsame row C ∨ hsame row Q ∨
                hsame row N ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont H0 H1 L ∧ Cont L I S ∧ Cont S T C ∧
              Cont C N consumerRead ∧ PkgSig bundle consumerRead pkg)
          hsame ∧ UnaryHistory consumerRead ∧ PkgSig bundle Q pkg ∧
            PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: FiniteHistLocalityPacketKernelCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier consumerRoute consumerPkg
  obtain ⟨h0Unary, h1Unary, invariantUnary, transportUnary, nameUnary, localityRoute,
    invariantRoute, transportRoute, provenancePkg, _namePkg⟩ := carrier
  have localityUnary : UnaryHistory L :=
    unary_cont_closed h0Unary h1Unary localityRoute
  have symmetryUnary : UnaryHistory S :=
    unary_cont_closed localityUnary invariantUnary invariantRoute
  have replayUnary : UnaryHistory C :=
    unary_cont_closed symmetryUnary transportUnary transportRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed replayUnary nameUnary consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row H0 ∨ hsame row H1 ∨ hsame row L ∨ hsame row I ∨
              hsame row S ∨ hsame row T ∨ hsame row C ∨ hsame row Q ∨
                hsame row N ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont H0 H1 L ∧ Cont L I S ∧ Cont S T C ∧
              Cont C N consumerRead ∧ PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerUnary⟩
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
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, localityRoute, invariantRoute, transportRoute, consumerRoute,
          consumerPkg⟩
  }
  exact ⟨cert, consumerUnary, provenancePkg, consumerPkg⟩

end BEDC.Derived.FiniteHistLocalityPacketUp
