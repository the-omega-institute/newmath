import BEDC.Derived.CompletelyRegularSpaceUp
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompletelyRegularSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompletelyRegularSpaceCarrier_real_valued_separation_window [AskSetup]
    [PackageSetup] {T R C F H K P N request separator sepRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletelyRegularSpaceCarrier T R C F H K P N bundle pkg ->
      Cont T R request ->
        Cont request C separator ->
          Cont separator F sepRead ->
            PkgSig bundle sepRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row sepRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row T ∨ hsame row R ∨ hsame row C ∨ hsame row F ∨
                      hsame row sepRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont T R request ∧ Cont request C separator ∧
                      Cont separator F sepRead ∧ PkgSig bundle sepRead pkg)
                  hsame ∧
                UnaryHistory request ∧ UnaryHistory separator ∧ UnaryHistory sepRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier requestRow separatorRow sepReadRow sepReadPkg
  obtain ⟨tUnary, rUnary, cUnary, fUnary, _hUnary, _kUnary, _pUnary, _nUnary,
    _carrierRequestRoute, _carrierReplayRoute, _carrierPkg⟩ := carrier
  have requestUnary : UnaryHistory request :=
    unary_cont_closed tUnary rUnary requestRow
  have separatorUnary : UnaryHistory separator :=
    unary_cont_closed requestUnary cUnary separatorRow
  have sepReadUnary : UnaryHistory sepRead :=
    unary_cont_closed separatorUnary fUnary sepReadRow
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row sepRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row T ∨ hsame row R ∨ hsame row C ∨ hsame row F ∨ hsame row sepRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont T R request ∧ Cont request C separator ∧
            Cont separator F sepRead ∧ PkgSig bundle sepRead pkg)
        hsame := by
    constructor
    · constructor
      · exact ⟨sepRead, hsame_refl sepRead, sepReadUnary⟩
      · intro row source
        exact hsame_refl row
      · intro row other same
        exact hsame_symm same
      · intro row other final same₁ same₂
        exact hsame_trans same₁ same₂
      · intro row other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, unary_transport source.right same⟩
    · intro row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    · intro row source
      exact ⟨source.right, requestRow, separatorRow, sepReadRow, sepReadPkg⟩
  exact ⟨cert, requestUnary, separatorUnary, sepReadUnary⟩

end BEDC.Derived.CompletelyRegularSpaceUp
