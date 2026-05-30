import BEDC.Derived.RiemannIntegralUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RiemannIntegralUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RiemannIntegralCarrier_darboux_gap_exactness [AskSetup] [PackageSetup]
    {M T F S D G R H C P N tagRead sumRead darbouxRead gapRead gapConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannIntegralPacket M T F S D G R H C P N bundle pkg ->
      Cont M T tagRead ->
        Cont F S sumRead ->
          Cont sumRead D darbouxRead ->
            Cont darbouxRead G gapRead ->
              Cont gapRead R gapConsumer ->
                PkgSig bundle gapConsumer pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row gapRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row S ∨ hsame row D ∨ hsame row G ∨
                          Cont darbouxRead G gapRead)
                      (fun row : BHist =>
                        PkgSig bundle P pkg ∧ PkgSig bundle gapConsumer pkg ∧
                          hsame row gapRead)
                      hsame ∧
                    UnaryHistory darbouxRead ∧ UnaryHistory gapRead ∧
                      UnaryHistory gapConsumer ∧ Cont sumRead D darbouxRead ∧
                        Cont darbouxRead G gapRead ∧ Cont gapRead R gapConsumer := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet tagRoute sumRoute darbouxRoute gapRoute consumerRoute consumerPkg
  obtain ⟨mUnary, tUnary, fUnary, sUnary, dUnary, gUnary, rUnary, _hUnary, _cUnary,
    provenanceUnary, _nUnary, _mtf, _fsd, _dgr, provenancePkg, _namePkg⟩ := packet
  have _tagUnary : UnaryHistory tagRead :=
    unary_cont_closed mUnary tUnary tagRoute
  have sumUnary : UnaryHistory sumRead :=
    unary_cont_closed fUnary sUnary sumRoute
  have darbouxUnary : UnaryHistory darbouxRead :=
    unary_cont_closed sumUnary dUnary darbouxRoute
  have gapUnary : UnaryHistory gapRead :=
    unary_cont_closed darbouxUnary gUnary gapRoute
  have consumerUnary : UnaryHistory gapConsumer :=
    unary_cont_closed gapUnary rUnary consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row gapRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row D ∨ hsame row G ∨ Cont darbouxRead G gapRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle gapConsumer pkg ∧ hsame row gapRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro gapRead ⟨hsame_refl gapRead, gapUnary⟩
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
        intro row other sameRows source
        have otherSame : hsame other gapRead :=
          hsame_trans (hsame_symm sameRows) source.left
        have otherUnary : UnaryHistory other :=
          unary_transport source.right sameRows
        exact ⟨otherSame, otherUnary⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr (Or.inr gapRoute))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, consumerPkg, source.left⟩
  }
  exact
    ⟨cert, darbouxUnary, gapUnary, consumerUnary, darbouxRoute, gapRoute, consumerRoute⟩

end BEDC.Derived.RiemannIntegralUp
