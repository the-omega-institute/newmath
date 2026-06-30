import BEDC.Derived.ConnectedIntervalUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
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

theorem ConnectedIntervalCarrier_obligation_closure_route [AskSetup] [PackageSetup]
    {L R W B S T E H C P N endpointRead branchRead nestedRead signRead sealRead
      closureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ConnectedIntervalCarrier L R W B S T E H C P N →
      Cont L R endpointRead →
        Cont endpointRead W branchRead →
          Cont branchRead B nestedRead →
            Cont nestedRead T signRead →
              Cont signRead E sealRead →
                Cont nestedRead sealRead closureRead →
                  PkgSig bundle P pkg →
                    PkgSig bundle N pkg →
                      PkgSig bundle closureRead pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row closureRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row L ∨ hsame row R ∨ hsame row W ∨ hsame row B ∨
                                hsame row S ∨ hsame row T ∨ hsame row E ∨ hsame row H ∨
                                  hsame row C ∨ hsame row P ∨ hsame row N ∨
                                    hsame row endpointRead ∨ hsame row branchRead ∨
                                      hsame row nestedRead ∨ hsame row signRead ∨
                                        hsame row sealRead ∨ hsame row closureRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont L R endpointRead ∧
                                Cont endpointRead W branchRead ∧ Cont branchRead B nestedRead ∧
                                  Cont nestedRead T signRead ∧ Cont signRead E sealRead ∧
                                    Cont nestedRead sealRead closureRead ∧
                                      PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                            hsame ∧
                          UnaryHistory closureRead ∧ PkgSig bundle closureRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory PkgSig
  intro carrier endpointRoute branchRoute nestedRoute signRoute sealRoute closureRoute
    provenancePkg namePkg closurePkg
  obtain ⟨leftUnary, _rightUnaryFromCarrier, windowUnary, signUnary, sealUnary, rootRoute,
    carrierSignRoute, _nameRoute, _provenanceRoute⟩ := carrier
  have carrierBranchUnary : UnaryHistory B :=
    unary_cont_closed leftUnary windowUnary rootRoute
  have carrierSignReadUnary : UnaryHistory T :=
    unary_cont_closed carrierBranchUnary signUnary carrierSignRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed leftUnary _rightUnaryFromCarrier endpointRoute
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed endpointUnary windowUnary branchRoute
  have nestedUnary : UnaryHistory nestedRead :=
    unary_cont_closed branchUnary carrierBranchUnary nestedRoute
  have signReadUnary : UnaryHistory signRead :=
    unary_cont_closed nestedUnary carrierSignReadUnary signRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed signReadUnary sealUnary sealRoute
  have closureUnary : UnaryHistory closureRead :=
    unary_cont_closed nestedUnary sealReadUnary closureRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro closureRead ⟨hsame_refl closureRead, closureUnary⟩
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
        right
        right
        right
        right
        right
        right
        right
        right
        right
        right
        right
        right
        exact source.left
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, endpointRoute, branchRoute, nestedRoute, signRoute, sealRoute,
            closureRoute, provenancePkg, namePkg⟩
    }
  · exact ⟨closureUnary, closurePkg⟩

end BEDC.Derived.ConnectedIntervalUp
