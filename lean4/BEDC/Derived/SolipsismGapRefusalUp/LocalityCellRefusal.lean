import BEDC.Derived.SolipsismGapRefusalUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.SolipsismGapRefusalUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary

theorem SolipsismGapRefusalUp_locality_cell_refusal
    {E R G H C P N evidenceRead residueRead : BHist} :
    UnaryHistory E ->
      UnaryHistory R ->
        UnaryHistory G ->
          UnaryHistory C ->
            Cont E R evidenceRead ->
              Cont G C residueRead ->
                UnaryHistory evidenceRead ∧ UnaryHistory residueRead ∧
                  List.Mem (solipsismGapRefusalEncodeBHist E)
                    (solipsismGapRefusalToEventFlow (SolipsismGapRefusalUp.mk E R G H C P N)) ∧
                    List.Mem (solipsismGapRefusalEncodeBHist R)
                      (solipsismGapRefusalToEventFlow
                        (SolipsismGapRefusalUp.mk E R G H C P N)) ∧
                      List.Mem (solipsismGapRefusalEncodeBHist G)
                        (solipsismGapRefusalToEventFlow
                          (SolipsismGapRefusalUp.mk E R G H C P N)) := by
  -- BEDC touchpoint anchor: BHist BMark Cont UnaryHistory
  intro EUnary RUnary GUnary CUnary evidenceCont residueCont
  have evidenceUnary : UnaryHistory evidenceRead :=
    unary_cont_closed EUnary RUnary evidenceCont
  have residueUnary : UnaryHistory residueRead :=
    unary_cont_closed GUnary CUnary residueCont
  have evidenceListed :
      List.Mem (solipsismGapRefusalEncodeBHist E)
        (solipsismGapRefusalToEventFlow (SolipsismGapRefusalUp.mk E R G H C P N)) := by
    change
      List.Mem (solipsismGapRefusalEncodeBHist E)
        [[BMark.b0], solipsismGapRefusalEncodeBHist E, [BMark.b1, BMark.b0],
          solipsismGapRefusalEncodeBHist R, [BMark.b1, BMark.b1, BMark.b0],
          solipsismGapRefusalEncodeBHist G,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          solipsismGapRefusalEncodeBHist H,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          solipsismGapRefusalEncodeBHist C,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          solipsismGapRefusalEncodeBHist P,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          solipsismGapRefusalEncodeBHist N]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have refusalListed :
      List.Mem (solipsismGapRefusalEncodeBHist R)
        (solipsismGapRefusalToEventFlow (SolipsismGapRefusalUp.mk E R G H C P N)) := by
    change
      List.Mem (solipsismGapRefusalEncodeBHist R)
        [[BMark.b0], solipsismGapRefusalEncodeBHist E, [BMark.b1, BMark.b0],
          solipsismGapRefusalEncodeBHist R, [BMark.b1, BMark.b1, BMark.b0],
          solipsismGapRefusalEncodeBHist G,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          solipsismGapRefusalEncodeBHist H,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          solipsismGapRefusalEncodeBHist C,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          solipsismGapRefusalEncodeBHist P,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          solipsismGapRefusalEncodeBHist N]
    exact
      List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self))
  have residueListed :
      List.Mem (solipsismGapRefusalEncodeBHist G)
        (solipsismGapRefusalToEventFlow (SolipsismGapRefusalUp.mk E R G H C P N)) := by
    change
      List.Mem (solipsismGapRefusalEncodeBHist G)
        [[BMark.b0], solipsismGapRefusalEncodeBHist E, [BMark.b1, BMark.b0],
          solipsismGapRefusalEncodeBHist R, [BMark.b1, BMark.b1, BMark.b0],
          solipsismGapRefusalEncodeBHist G,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          solipsismGapRefusalEncodeBHist H,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          solipsismGapRefusalEncodeBHist C,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          solipsismGapRefusalEncodeBHist P,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          solipsismGapRefusalEncodeBHist N]
    exact
      List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ List.mem_cons_self))))
  exact ⟨evidenceUnary, residueUnary, evidenceListed, refusalListed, residueListed⟩

end BEDC.Derived.SolipsismGapRefusalUp
