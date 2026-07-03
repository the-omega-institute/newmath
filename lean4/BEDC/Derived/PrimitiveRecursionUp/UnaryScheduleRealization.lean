import BEDC.Derived.PrimitiveRecursionUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PrimitiveRecursionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PrimitiveRecursionCarrier [AskSetup] [PackageSetup]
    (D S T U W Q H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory D ∧ UnaryHistory S ∧ UnaryHistory T ∧ UnaryHistory U ∧
    UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem PrimitiveRecursionCarrier_unary_schedule_realization [AskSetup] [PackageSetup]
    {D S T U W Q H C P N seedRead stepRead traceRead scheduleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PrimitiveRecursionCarrier D S T U W Q H C P N bundle pkg ->
      Cont D S seedRead ->
        Cont seedRead T stepRead ->
          Cont stepRead U traceRead ->
            Cont traceRead W scheduleRead ->
              PkgSig bundle scheduleRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row scheduleRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row D ∨ hsame row S ∨ hsame row T ∨ hsame row U ∨
                        hsame row W ∨ hsame row Q ∨ hsame row seedRead ∨
                          hsame row stepRead ∨ hsame row traceRead ∨
                            hsame row scheduleRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont D S seedRead ∧ Cont seedRead T stepRead ∧
                        Cont stepRead U traceRead ∧ Cont traceRead W scheduleRead ∧
                          PkgSig bundle scheduleRead pkg)
                    hsame ∧
                  UnaryHistory seedRead ∧ UnaryHistory stepRead ∧
                    UnaryHistory traceRead ∧ UnaryHistory scheduleRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier seedRoute stepRoute traceRoute scheduleRoute schedulePkg
  obtain ⟨dUnary, sUnary, tUnary, uUnary, wUnary, _qUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _pPkg, _nPkg⟩ := carrier
  have seedUnary : UnaryHistory seedRead :=
    unary_cont_closed dUnary sUnary seedRoute
  have stepUnary : UnaryHistory stepRead :=
    unary_cont_closed seedUnary tUnary stepRoute
  have traceUnary : UnaryHistory traceRead :=
    unary_cont_closed stepUnary uUnary traceRoute
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed traceUnary wUnary scheduleRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scheduleRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row S ∨ hsame row T ∨ hsame row U ∨ hsame row W ∨
              hsame row Q ∨ hsame row seedRead ∨ hsame row stepRead ∨
                hsame row traceRead ∨ hsame row scheduleRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D S seedRead ∧ Cont seedRead T stepRead ∧
              Cont stepRead U traceRead ∧ Cont traceRead W scheduleRead ∧
                PkgSig bundle scheduleRead pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨scheduleRead, hsame_refl scheduleRead, scheduleUnary⟩
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
                  (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, seedRoute, stepRoute, traceRoute, scheduleRoute, schedulePkg⟩
  }
  exact ⟨cert, seedUnary, stepUnary, traceUnary, scheduleUnary⟩

theorem PrimitiveRecursionStreamScheduleHandoff [AskSetup] [PackageSetup]
    {D S T U W Q H C P N seedRead stepRead traceRead scheduleRead consumerRead
      replay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PrimitiveRecursionCarrier D S T U W Q H C P N bundle pkg →
      Cont D S seedRead →
        Cont seedRead T stepRead →
          Cont stepRead U traceRead →
            Cont traceRead W scheduleRead →
              Cont scheduleRead Q consumerRead →
                Cont consumerRead C replay →
                  PkgSig bundle P pkg →
                    PkgSig bundle N pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row D ∨ hsame row S ∨ hsame row T ∨ hsame row U ∨
                              hsame row W ∨ hsame row Q ∨ hsame row H ∨
                                hsame row C ∨ hsame row P ∨ hsame row N ∨
                                  hsame row scheduleRead ∨ hsame row consumerRead ∨
                                    hsame row replay)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont D S seedRead ∧
                              Cont seedRead T stepRead ∧ Cont stepRead U traceRead ∧
                                Cont traceRead W scheduleRead ∧
                                  Cont scheduleRead Q consumerRead ∧
                                    Cont consumerRead C replay ∧
                                      PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                          hsame ∧
                        UnaryHistory consumerRead ∧ UnaryHistory replay := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier seedRoute stepRoute traceRoute scheduleRoute consumerRoute replayRoute
    provenancePkg namePkg
  obtain ⟨dUnary, sUnary, tUnary, uUnary, wUnary, qUnary, _hUnary, cUnary, _pUnary,
    _nUnary, _carrierProvenancePkg, _carrierNamePkg⟩ := carrier
  have seedUnary : UnaryHistory seedRead :=
    unary_cont_closed dUnary sUnary seedRoute
  have stepUnary : UnaryHistory stepRead :=
    unary_cont_closed seedUnary tUnary stepRoute
  have traceUnary : UnaryHistory traceRead :=
    unary_cont_closed stepUnary uUnary traceRoute
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed traceUnary wUnary scheduleRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed scheduleUnary qUnary consumerRoute
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed consumerUnary cUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row S ∨ hsame row T ∨ hsame row U ∨ hsame row W ∨
              hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row scheduleRead ∨ hsame row consumerRead ∨ hsame row replay)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D S seedRead ∧ Cont seedRead T stepRead ∧
              Cont stepRead U traceRead ∧ Cont traceRead W scheduleRead ∧
                Cont scheduleRead Q consumerRead ∧ Cont consumerRead C replay ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨consumerRead, hsame_refl consumerRead, consumerUnary⟩
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
                          (Or.inr (Or.inr (Or.inl source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, seedRoute, stepRoute, traceRoute, scheduleRoute, consumerRoute,
          replayRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, consumerUnary, replayUnary⟩

end BEDC.Derived.PrimitiveRecursionUp
