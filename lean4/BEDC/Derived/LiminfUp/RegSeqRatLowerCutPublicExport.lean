import BEDC.Derived.LiminfUp

namespace BEDC.Derived.LiminfUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LiminfRegSeqRatLowerCutPublicExport [AskSetup] [PackageSetup]
    {sequence lowerCut dyadic terminal transport replay provenance localName sealRead
      regSeqExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LiminfCarrier sequence lowerCut dyadic terminal transport replay provenance localName
        bundle pkg ->
      Cont terminal transport sealRead ->
        Cont sealRead localName regSeqExport ->
          PkgSig bundle provenance pkg ->
            PkgSig bundle regSeqExport pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row regSeqExport ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row sequence ∨ hsame row lowerCut ∨ hsame row dyadic ∨
                      hsame row terminal ∨ hsame row sealRead ∨ hsame row regSeqExport)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont sequence lowerCut dyadic ∧
                      Cont terminal transport sealRead ∧
                        Cont sealRead localName regSeqExport ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle regSeqExport pkg)
                  hsame ∧ UnaryHistory sealRead ∧ UnaryHistory regSeqExport := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier terminalSeal sealRegular provenancePkg regSeqPkg
  have sequenceUnary : UnaryHistory sequence := carrier.left
  have lowerCutUnary : UnaryHistory lowerCut := carrier.right.left
  have dyadicUnary : UnaryHistory dyadic := carrier.right.right.left
  have terminalUnary : UnaryHistory terminal := carrier.right.right.right.left
  have transportUnary : UnaryHistory transport := carrier.right.right.right.right.left
  have localNameUnary : UnaryHistory localName :=
    carrier.right.right.right.right.right.right.right.left
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed terminalUnary transportUnary terminalSeal
  have regSeqUnary : UnaryHistory regSeqExport :=
    unary_cont_closed sealUnary localNameUnary sealRegular
  have sequenceRoute : Cont sequence lowerCut dyadic :=
    carrier.right.right.right.right.right.right.right.right.left
  have source :
      (fun row : BHist => hsame row regSeqExport ∧ UnaryHistory row) regSeqExport := by
    exact ⟨hsame_refl regSeqExport, regSeqUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row regSeqExport ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sequence ∨ hsame row lowerCut ∨ hsame row dyadic ∨
              hsame row terminal ∨ hsame row sealRead ∨ hsame row regSeqExport)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont sequence lowerCut dyadic ∧
              Cont terminal transport sealRead ∧ Cont sealRead localName regSeqExport ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle regSeqExport pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro regSeqExport source
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
          intro _row _other sameRows sourceRows
          constructor
          · exact hsame_trans (hsame_symm sameRows) sourceRows.left
          · exact unary_transport sourceRows.right sameRows
      }
      pattern_sound := by
        intro _row sourceRows
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRows.left))))
      ledger_sound := by
        intro _row sourceRows
        exact ⟨sourceRows.right, sequenceRoute, terminalSeal, sealRegular, provenancePkg,
          regSeqPkg⟩
    }
  exact ⟨cert, sealUnary, regSeqUnary⟩

end BEDC.Derived.LiminfUp
