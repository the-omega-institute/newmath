import BEDC.Derived.BoundedRealSequenceUp.NameCertObligations

namespace BEDC.Derived.BoundedRealSequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedRealSequenceCarrier_window_localization [AskSetup] [PackageSetup]
    {S W Q R I H C P N windowRead readbackRead sealRead boundRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NameCertObligations.BoundedRealSequenceCarrier S W Q R I H C P N bundle pkg ->
      Cont S W windowRead ->
        Cont windowRead Q readbackRead ->
          Cont readbackRead R sealRead ->
            Cont sealRead I boundRead ->
              PkgSig bundle boundRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row boundRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row S ∨ hsame row W ∨ hsame row Q ∨ hsame row R ∨
                        hsame row I ∨ hsame row boundRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle boundRead pkg)
                    hsame ∧
                  UnaryHistory windowRead ∧ UnaryHistory readbackRead ∧
                    UnaryHistory sealRead ∧ UnaryHistory boundRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier sourceWindow windowReadback readbackSeal sealBound boundPkg
  obtain ⟨sourceUnary, windowUnary, readbackUnary, realUnary, intervalUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localCertUnary, _intervalRoute,
    _transportSame, provenancePkg, _localCertPkg⟩ := carrier
  have windowUnaryRead : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary windowUnary sourceWindow
  have readbackUnaryRead : UnaryHistory readbackRead :=
    unary_cont_closed windowUnaryRead readbackUnary windowReadback
  have sealUnaryRead : UnaryHistory sealRead :=
    unary_cont_closed readbackUnaryRead realUnary readbackSeal
  have boundUnaryRead : UnaryHistory boundRead :=
    unary_cont_closed sealUnaryRead intervalUnary sealBound
  have sourceBound :
      (fun row : BHist => hsame row boundRead ∧ UnaryHistory row) boundRead := by
    exact ⟨hsame_refl boundRead, boundUnaryRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row W ∨ hsame row Q ∨ hsame row R ∨
              hsame row I ∨ hsame row boundRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle boundRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundRead sourceBound
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, boundPkg⟩
  }
  exact ⟨cert, windowUnaryRead, readbackUnaryRead, sealUnaryRead, boundUnaryRead⟩

end BEDC.Derived.BoundedRealSequenceUp
