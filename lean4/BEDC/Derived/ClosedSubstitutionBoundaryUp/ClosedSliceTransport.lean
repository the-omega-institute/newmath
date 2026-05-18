import BEDC.Derived.ClosedSubstitutionBoundaryUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ClosedSubstitutionBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedSubstitutionBoundary_closed_slice_transport
    [AskSetup] [PackageSetup]
    {T D V K R Q H C P N T' D' V' K' R' Q' H' C' P' N'
      substituteRead publicRead : BHist} :
    UnaryHistory T →
      UnaryHistory D →
        UnaryHistory V →
          UnaryHistory K →
            UnaryHistory R →
              UnaryHistory Q →
                UnaryHistory C →
                  UnaryHistory N →
                    hsame T T' →
                      hsame D D' →
                        hsame V V' →
                          hsame K K' →
                            hsame R R' →
                              hsame Q Q' →
                                hsame C C' →
                                  hsame P P' →
                                    hsame N N' →
                                      Cont K Q substituteRead →
                                        Cont substituteRead C publicRead →
                                          UnaryHistory Q' ∧ UnaryHistory C' ∧
                                            Cont K' Q' substituteRead ∧
                                              Cont substituteRead C' publicRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro _unaryT _unaryD _unaryV _unaryK _unaryR unaryQ unaryC _unaryN
    _sameT _sameD _sameV sameK _sameR sameQ sameC _sameP _sameN
    substituteRoute publicRoute
  have unaryQ' : UnaryHistory Q' := unary_transport unaryQ sameQ
  have unaryC' : UnaryHistory C' := unary_transport unaryC sameC
  have substituteRoute' : Cont K' Q' substituteRead :=
    cont_hsame_transport sameK sameQ (hsame_refl substituteRead) substituteRoute
  have publicRoute' : Cont substituteRead C' publicRead :=
    cont_hsame_transport (hsame_refl substituteRead) sameC (hsame_refl publicRead)
      publicRoute
  exact ⟨unaryQ', unaryC', substituteRoute', publicRoute'⟩

end BEDC.Derived.ClosedSubstitutionBoundaryUp
