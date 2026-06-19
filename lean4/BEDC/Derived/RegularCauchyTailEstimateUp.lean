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

theorem RegularCauchyTailEstimateNameCertObligations
    {M W D R E H C P N thresholdRead toleranceRead sealRead : BHist} :
    UnaryHistory M →
      UnaryHistory W →
        UnaryHistory D →
          UnaryHistory R →
            UnaryHistory E →
              Cont M W thresholdRead →
                Cont thresholdRead D toleranceRead →
                  Cont toleranceRead R sealRead →
                    SemanticNameCert
                        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row M ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
                            hsame row E ∨ hsame row sealRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont M W thresholdRead ∧
                            Cont thresholdRead D toleranceRead ∧
                              Cont toleranceRead R sealRead)
                        hsame ∧
                      UnaryHistory thresholdRead ∧ UnaryHistory toleranceRead ∧
                        UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory SemanticNameCert
  intro unaryM unaryW unaryD unaryR _unaryE thresholdRoute toleranceRoute sealRoute
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed unaryM unaryW thresholdRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed thresholdUnary unaryD toleranceRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary unaryR sealRoute
  have adminRows : hsame H H ∧ hsame C C ∧ hsame P P ∧ hsame N N := by
    exact
      ⟨hsame_refl H, hsame_refl C, hsame_refl P, hsame_refl N⟩
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealUnary⟩
  have core :
      NameCert
        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro sealRead sourceSeal
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    }
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
              hsame row E ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M W thresholdRead ∧
              Cont thresholdRead D toleranceRead ∧ Cont toleranceRead R sealRead)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro row source
        cases adminRows with
        | intro _sameH adminRest =>
            cases adminRest with
            | intro _sameC adminTail =>
                cases adminTail with
                | intro _sameP _sameN =>
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, thresholdRoute, toleranceRoute, sealRoute⟩
    }
  exact ⟨cert, thresholdUnary, toleranceUnary, sealUnary⟩

theorem RegularCauchyTailEstimateCarrier_tail_dominance [AskSetup] [PackageSetup]
    {M W D R E H C P N thresholdRead toleranceRead sealRead laterRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailEstimateCarrier M W D R E H C P N bundle pkg ->
      Cont M W thresholdRead ->
        Cont thresholdRead D toleranceRead ->
          Cont toleranceRead R sealRead ->
            Cont sealRead H laterRead ->
              PkgSig bundle P pkg ->
                PkgSig bundle N pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row laterRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row M ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
                          hsame row E ∨ hsame row sealRead ∨ hsame row laterRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont M W thresholdRead ∧
                          Cont thresholdRead D toleranceRead ∧
                            Cont toleranceRead R sealRead ∧ Cont sealRead H laterRead ∧
                              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                      hsame ∧
                    UnaryHistory laterRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier routeThreshold routeTolerance routeSeal routeLater provenancePkg namePkg
  obtain ⟨unaryM, unaryW, unaryD, unaryR, _unaryE, unaryH, _unaryC, _unaryP,
    _unaryN, _carrierPkg, _carrierName⟩ := carrier
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed unaryM unaryW routeThreshold
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed thresholdUnary unaryD routeTolerance
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary unaryR routeSeal
  have laterUnary : UnaryHistory laterRead :=
    unary_cont_closed sealUnary unaryH routeLater
  have sourceLater :
      (fun row : BHist => hsame row laterRead ∧ UnaryHistory row) laterRead := by
    exact ⟨hsame_refl laterRead, laterUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row laterRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
              hsame row E ∨ hsame row sealRead ∨ hsame row laterRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M W thresholdRead ∧
              Cont thresholdRead D toleranceRead ∧ Cont toleranceRead R sealRead ∧
                Cont sealRead H laterRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro laterRead sourceLater
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, routeThreshold, routeTolerance, routeSeal, routeLater,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, laterUnary⟩

end BEDC.Derived.RegularCauchyTailEstimateUp
