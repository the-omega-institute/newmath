import BEDC.Derived.RationalStreamUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RationalStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RationalStreamPacket_namecert_seed_obligations [AskSetup] [PackageSetup]
    {index schedule pointRows classifierRows transportRows contRows provenance nameRow window
      seedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalStreamPacket index schedule pointRows classifierRows transportRows contRows provenance
        nameRow window bundle pkg ->
      Cont nameRow window seedRead ->
        PkgSig bundle seedRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row seedRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row index ∨ hsame row schedule ∨ hsame row pointRows ∨
                  hsame row classifierRows ∨ hsame row seedRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont index schedule window ∧
                  Cont window pointRows classifierRows ∧ Cont nameRow window seedRead ∧
                    PkgSig bundle seedRead pkg)
              hsame ∧
            UnaryHistory window ∧ UnaryHistory classifierRows ∧ UnaryHistory seedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro packet seedReadRow seedReadPkg
  obtain ⟨indexUnary, scheduleUnary, _pointRowsUnary, classifierRowsUnary, transportRowsUnary,
    provenanceUnary, windowRow, classifierRowsRow, contRowsRow, nameRowRow, _namePkg⟩ :=
    packet
  have windowUnary : UnaryHistory window :=
    unary_cont_closed indexUnary scheduleUnary windowRow
  have contRowsUnary : UnaryHistory contRows :=
    unary_cont_closed classifierRowsUnary transportRowsUnary contRowsRow
  have nameRowUnary : UnaryHistory nameRow :=
    unary_cont_closed contRowsUnary provenanceUnary nameRowRow
  have seedReadUnary : UnaryHistory seedRead :=
    unary_cont_closed nameRowUnary windowUnary seedReadRow
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row seedRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row index ∨ hsame row schedule ∨ hsame row pointRows ∨
            hsame row classifierRows ∨ hsame row seedRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont index schedule window ∧
            Cont window pointRows classifierRows ∧ Cont nameRow window seedRead ∧
              PkgSig bundle seedRead pkg)
        hsame := by
    constructor
    · constructor
      · exact ⟨seedRead, hsame_refl seedRead, seedReadUnary⟩
      · intro row source
        exact hsame_refl row
      · intro row other same
        exact hsame_symm same
      · intro row other final same₁ same₂
        exact hsame_trans same₁ same₂
      · intro row other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, unary_transport source.right same⟩
    · intro row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    · intro row source
      exact ⟨source.right, windowRow, classifierRowsRow, seedReadRow, seedReadPkg⟩
  exact ⟨cert, windowUnary, classifierRowsUnary, seedReadUnary⟩

end BEDC.Derived.RationalStreamUp
