import BEDC.Derived.DendriteUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DendriteUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DendriteCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {K L P T E A C H R G Q N endpointRead arcRead cutpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory K ->
      UnaryHistory L ->
        UnaryHistory P ->
          UnaryHistory T ->
            UnaryHistory E ->
              UnaryHistory A ->
                UnaryHistory C ->
                  UnaryHistory H ->
                    UnaryHistory R ->
                      UnaryHistory G ->
                        UnaryHistory Q ->
                          UnaryHistory N ->
                            Cont K L P ->
                              Cont T E A ->
                                Cont A C endpointRead ->
                                  Cont endpointRead H arcRead ->
                                    Cont arcRead R cutpointRead ->
                                      PkgSig bundle G pkg ->
                                        PkgSig bundle N pkg ->
                                          SemanticNameCert
                                            (fun row : BHist => hsame row N ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row K ∨ hsame row L ∨ hsame row P ∨
                                                hsame row T ∨ hsame row E ∨ hsame row A ∨
                                                  hsame row C ∨ hsame row endpointRead ∨
                                                    hsame row arcRead ∨
                                                      hsame row cutpointRead ∨ hsame row N)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧ Cont K L P ∧ Cont T E A ∧
                                                Cont A C endpointRead ∧
                                                  Cont endpointRead H arcRead ∧
                                                    Cont arcRead R cutpointRead ∧
                                                      PkgSig bundle G pkg ∧ PkgSig bundle N pkg)
                                            hsame := by
  -- BEDC touchpoint anchor: DendriteUp BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro _kUnary _lUnary _pUnary _tUnary _eUnary _aUnary _cUnary _hUnary _rUnary
    _gUnary _qUnary nUnary compactRoute treeRoute endpointRoute arcRoute cutpointRoute
    provenancePkg namePkg
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro N ⟨hsame_refl N, nUnary⟩
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
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, compactRoute, treeRoute, endpointRoute, arcRoute, cutpointRoute,
          provenancePkg, namePkg⟩
  }

end BEDC.Derived.DendriteUp
