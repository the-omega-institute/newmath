import BEDC.Derived.FareySequenceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceRegularReadbackApproximationBridge [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N boundaryRead denominatorRead toleranceRead
      windowRead readbackRead approximationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg →
      Cont B A boundaryRead →
        Cont boundaryRead L denominatorRead →
          Cont denominatorRead T toleranceRead →
            Cont toleranceRead W windowRead →
              Cont windowRead R readbackRead →
                Cont readbackRead G approximationRead →
                  PkgSig bundle P pkg →
                    PkgSig bundle N pkg →
                      SemanticNameCert
                        (fun row : BHist => hsame row approximationRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row B ∨ hsame row A ∨ hsame row L ∨ hsame row T ∨
                            hsame row W ∨ hsame row R ∨ hsame row G ∨
                              hsame row approximationRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont windowRead R readbackRead ∧
                            Cont readbackRead G approximationRead ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle N pkg)
                        hsame ∧ UnaryHistory readbackRead ∧ UnaryHistory approximationRead := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier boundaryRoute denominatorRoute toleranceRoute windowRoute readbackRoute
    approximationRoute provenancePkg namePkg
  obtain ⟨bUnary, aUnary, _mUnary, lUnary, tUnary, _sUnary, _dUnary, _qUnary, wUnary,
    rUnary, gUnary, _eUnary, _hUnary, _cUnary, _pUnary, _nUnary, _aEmpty, _sEmpty,
    _mEmpty, _gEmpty, _eEmpty, _carrierPkg⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed bUnary aUnary boundaryRoute
  have denominatorUnary : UnaryHistory denominatorRead :=
    unary_cont_closed boundaryUnary lUnary denominatorRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed denominatorUnary tUnary toleranceRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed toleranceUnary wUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary rUnary readbackRoute
  have approximationUnary : UnaryHistory approximationRead :=
    unary_cont_closed readbackUnary gUnary approximationRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row approximationRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row B ∨ hsame row A ∨ hsame row L ∨ hsame row T ∨ hsame row W ∨
            hsame row R ∨ hsame row G ∨ hsame row approximationRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont windowRead R readbackRead ∧
            Cont readbackRead G approximationRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro approximationRead
        ⟨hsame_refl approximationRead, approximationUnary⟩
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
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, readbackRoute, approximationRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, readbackUnary, approximationUnary⟩

end BEDC.Derived.FareySequenceUp
