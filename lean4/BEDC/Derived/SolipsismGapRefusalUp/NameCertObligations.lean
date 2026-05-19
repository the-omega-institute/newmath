import BEDC.Derived.SolipsismGapRefusalUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SolipsismGapRefusalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SolipsismGapRefusalNameCertObligations [AskSetup] [PackageSetup]
    {E R G H C P N evidenceRead residueRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory E -> UnaryHistory R -> UnaryHistory G -> UnaryHistory C -> UnaryHistory N ->
      Cont E R evidenceRead -> Cont G C residueRead -> Cont C N namedRead ->
        PkgSig bundle namedRead pkg ->
          solipsismGapRefusalToEventFlow (SolipsismGapRefusalUp.mk E R G H C P N) =
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
                solipsismGapRefusalEncodeBHist N] ∧
            UnaryHistory evidenceRead ∧ UnaryHistory residueRead ∧ UnaryHistory namedRead ∧
              SemanticNameCert
                (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row evidenceRead ∨ hsame row residueRead ∨ hsame row namedRead)
                (fun row : BHist => PkgSig bundle namedRead pkg ∧ hsame row namedRead)
                hsame := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro EUnary RUnary GUnary CUnary NUnary evidenceCont residueCont namedCont namedPkg
  have evidenceUnary : UnaryHistory evidenceRead :=
    unary_cont_closed EUnary RUnary evidenceCont
  have residueUnary : UnaryHistory residueRead :=
    unary_cont_closed GUnary CUnary residueCont
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed CUnary NUnary namedCont
  have sourceNamed :
      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row) namedRead := by
    exact ⟨hsame_refl namedRead, namedUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row evidenceRead ∨ hsame row residueRead ∨ hsame row namedRead)
        (fun row : BHist => PkgSig bundle namedRead pkg ∧ hsame row namedRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro namedRead sourceNamed
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr source.left)
      ledger_sound := by
        intro _row source
        exact ⟨namedPkg, source.left⟩
    }
  exact ⟨rfl, evidenceUnary, residueUnary, namedUnary, cert⟩

end BEDC.Derived.SolipsismGapRefusalUp
