import BEDC.Derived.LocatedLimitUp.NameCertObligations
import BEDC.Derived.LocatedLimitUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedLimit_regseqrat_readback_stability [AskSetup] [PackageSetup]
    {S M T Q E H C P N S' M' T' Q' scheduleRead scheduleRead' readbackRead
      readbackRead' : BHist}
    (sameS : hsame S S') (sameM : hsame M M') (sameT : hsame T T')
    (sameQ : hsame Q Q') (leftSchedule : Cont S M scheduleRead)
    (rightSchedule : Cont S' M' scheduleRead')
    (leftReadback : Cont scheduleRead T readbackRead)
    (rightReadback : Cont scheduleRead' T' readbackRead') :
    hsame scheduleRead scheduleRead' ∧ hsame readbackRead readbackRead' := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  have sameSchedule : hsame scheduleRead scheduleRead' :=
    cont_respects_hsame sameS sameM leftSchedule rightSchedule
  have sameReadback : hsame readbackRead readbackRead' :=
    cont_respects_hsame sameSchedule sameT leftReadback rightReadback
  exact And.intro sameSchedule sameReadback

theorem LocatedLimitCarrier_regseqrat_readback_stability [AskSetup] [PackageSetup]
    {S M T Q E H C P N scheduleRead readbackRead sealRead stableRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont S M scheduleRead →
      Cont scheduleRead T readbackRead →
        Cont readbackRead Q sealRead →
          Cont Q H stableRead →
            PkgSig bundle P pkg →
              UnaryHistory S →
                UnaryHistory M →
                  UnaryHistory T →
                    UnaryHistory Q →
                      UnaryHistory H →
                        SemanticNameCert
                            (fun row : BHist => hsame row stableRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row S ∨ hsame row M ∨ hsame row T ∨ hsame row Q ∨
                                hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                                  hsame row N ∨ hsame row scheduleRead ∨
                                    hsame row readbackRead ∨ hsame row sealRead ∨
                                      hsame row stableRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont S M scheduleRead ∧
                                Cont scheduleRead T readbackRead ∧
                                  Cont readbackRead Q sealRead ∧ Cont Q H stableRead ∧
                                    PkgSig bundle P pkg)
                            hsame ∧
                          UnaryHistory scheduleRead ∧ UnaryHistory readbackRead ∧
                            UnaryHistory sealRead ∧ UnaryHistory stableRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro scheduleCont readbackCont sealCont stableCont pkgP unaryS unaryM unaryT unaryQ unaryH
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed unaryS unaryM scheduleCont
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed scheduleUnary unaryT readbackCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary unaryQ sealCont
  have stableUnary : UnaryHistory stableRead :=
    unary_cont_closed unaryQ unaryH stableCont
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row stableRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row M ∨ hsame row T ∨ hsame row Q ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row scheduleRead ∨ hsame row readbackRead ∨ hsame row sealRead ∨
                  hsame row stableRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S M scheduleRead ∧ Cont scheduleRead T readbackRead ∧
              Cont readbackRead Q sealRead ∧ Cont Q H stableRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro stableRead ⟨hsame_refl stableRead, stableUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, scheduleCont, readbackCont, sealCont, stableCont, pkgP⟩
  }
  exact ⟨cert, scheduleUnary, readbackUnary, sealUnary, stableUnary⟩

end BEDC.Derived.LocatedLimitUp
