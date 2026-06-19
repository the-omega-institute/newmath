import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyTailEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyTailEstimateCarrier [AskSetup] [PackageSetup]
    (M W D R E H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory M ∧ UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory R ∧
    UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem RegularCauchyTailEstimateCarrier_real_seal_route [AskSetup] [PackageSetup]
    {M W D R E H C P N thresholdRead regularRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailEstimateCarrier M W D R E H C P N bundle pkg →
      Cont M W thresholdRead →
        Cont thresholdRead D regularRead →
          Cont regularRead R sealRead →
            PkgSig bundle P pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row E ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row M ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
                      hsame row E ∨ hsame row sealRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont M W thresholdRead ∧
                      Cont thresholdRead D regularRead ∧ Cont regularRead R sealRead ∧
                        PkgSig bundle P pkg)
                  hsame ∧
                UnaryHistory thresholdRead ∧ UnaryHistory regularRead ∧
                  UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier routeThreshold routeRegular routeSeal provenance
  obtain ⟨unaryM, unaryW, unaryD, unaryR, unaryE, _unaryH, _unaryC, _unaryP,
    _unaryN, _carrierPkg, _carrierName⟩ := carrier
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed unaryM unaryW routeThreshold
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed thresholdUnary unaryD routeRegular
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularUnary unaryR routeSeal
  have sourceE :
      (fun row : BHist => hsame row E ∧ UnaryHistory row) E := by
    exact ⟨hsame_refl E, unaryE⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row E ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
              hsame row E ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M W thresholdRead ∧
              Cont thresholdRead D regularRead ∧ Cont regularRead R sealRead ∧
                PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro E sourceE
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
      right
      right
      right
      right
      exact Or.inl source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, routeThreshold, routeRegular, routeSeal, provenance⟩
  }
  exact ⟨cert, thresholdUnary, regularUnary, sealUnary⟩

end BEDC.Derived.RegularCauchyTailEstimateUp
