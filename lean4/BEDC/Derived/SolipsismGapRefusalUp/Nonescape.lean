import BEDC.Derived.SolipsismGapRefusalUp.NameCertObligations

namespace BEDC.Derived.SolipsismGapRefusalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SolipsismGapRefusalUp_nonescape [AskSetup] [PackageSetup]
    {E R G H C P N evidenceRead residueRead namedRead escapeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory E →
      UnaryHistory R →
        UnaryHistory G →
          UnaryHistory C →
            UnaryHistory N →
              Cont E R evidenceRead →
                Cont G C residueRead →
                  Cont C N namedRead →
                    Cont namedRead G escapeRead →
                      PkgSig bundle escapeRead pkg →
                        UnaryHistory evidenceRead ∧ UnaryHistory residueRead ∧
                          UnaryHistory namedRead ∧ UnaryHistory escapeRead ∧
                            Cont namedRead G escapeRead ∧ PkgSig bundle escapeRead pkg ∧
                              List.Mem (solipsismGapRefusalEncodeBHist R)
                                (solipsismGapRefusalToEventFlow
                                  (SolipsismGapRefusalUp.mk E R G H C P N)) := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle PkgSig UnaryHistory
  intro EUnary RUnary GUnary CUnary NUnary evidenceCont residueCont namedCont escapeCont
    escapePkg
  have evidenceReadUnary : UnaryHistory evidenceRead :=
    unary_cont_closed EUnary RUnary evidenceCont
  have residueReadUnary : UnaryHistory residueRead :=
    unary_cont_closed GUnary CUnary residueCont
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed CUnary NUnary namedCont
  have escapeReadUnary : UnaryHistory escapeRead :=
    unary_cont_closed namedReadUnary GUnary escapeCont
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
  exact
    ⟨evidenceReadUnary, residueReadUnary, namedReadUnary, escapeReadUnary, escapeCont,
      escapePkg, refusalListed⟩

end BEDC.Derived.SolipsismGapRefusalUp
