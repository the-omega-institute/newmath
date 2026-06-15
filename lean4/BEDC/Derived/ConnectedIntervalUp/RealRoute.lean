import BEDC.Derived.ConnectedIntervalUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ConnectedIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ConnectedIntervalRealRoute [AskSetup] [PackageSetup]
    {L R W B S T E H C P N endpointRead branchRead nestedRead signRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L →
      UnaryHistory R →
        UnaryHistory W →
          UnaryHistory B →
            UnaryHistory S →
              UnaryHistory T →
                UnaryHistory E →
                  UnaryHistory H →
                    UnaryHistory C →
                      UnaryHistory P →
                        UnaryHistory N →
                          Cont L R endpointRead →
                            Cont endpointRead W branchRead →
                              Cont branchRead B nestedRead →
                                Cont nestedRead T signRead →
                                  Cont signRead E sealRead →
                                    PkgSig bundle P pkg →
                                      PkgSig bundle N pkg →
                                        SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row sealRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row L ∨ hsame row R ∨ hsame row W ∨
                                              hsame row B ∨ hsame row S ∨ hsame row T ∨
                                                hsame row E ∨ hsame row H ∨ hsame row C ∨
                                                  hsame row P ∨ hsame row N ∨
                                                    hsame row endpointRead ∨
                                                      hsame row branchRead ∨
                                                        hsame row nestedRead ∨
                                                          hsame row signRead ∨
                                                            hsame row sealRead)
                                          (fun row : BHist =>
                                            hsame row sealRead ∧ Cont L R endpointRead ∧
                                              Cont endpointRead W branchRead ∧
                                                Cont branchRead B nestedRead ∧
                                                  Cont nestedRead T signRead ∧
                                                    Cont signRead E sealRead ∧
                                                      PkgSig bundle P pkg ∧
                                                        PkgSig bundle N pkg)
                                          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro lUnary rUnary wUnary bUnary _sUnary tUnary eUnary _hUnary _cUnary _pUnary
    _nUnary endpointCont branchCont nestedCont signCont sealCont provenancePkg namePkg
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed lUnary rUnary endpointCont
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed endpointUnary wUnary branchCont
  have nestedUnary : UnaryHistory nestedRead :=
    unary_cont_closed branchUnary bUnary nestedCont
  have signUnary : UnaryHistory signRead :=
    unary_cont_closed nestedUnary tUnary signCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed signUnary eUnary sealCont
  exact {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr source.left))))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.left, endpointCont, branchCont, nestedCont, signCont, sealCont,
          provenancePkg, namePkg⟩
  }

end BEDC.Derived.ConnectedIntervalUp
