import BEDC.Derived.FastCauchyCompletionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FastCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FastCauchyCompletionModulusRealSeal [AskSetup] [PackageSetup]
    {modulus stream dyadic regular realSeal transport replay provenance localName
      realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont modulus stream dyadic ->
      Cont dyadic regular realSeal ->
        Cont realSeal replay realRead ->
          hsame transport localName ->
            UnaryHistory modulus ->
              UnaryHistory stream ->
                UnaryHistory regular ->
                  UnaryHistory replay ->
                    PkgSig bundle realRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row modulus ∨ hsame row stream ∨
                              hsame row dyadic ∨ hsame row regular ∨
                                hsame row realSeal ∨ hsame row replay ∨
                                  hsame row realRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle realRead pkg)
                          hsame ∧
                        UnaryHistory dyadic ∧ UnaryHistory realSeal ∧
                          UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg PkgSig SemanticNameCert UnaryHistory
  intro modulusStreamDyadic dyadicRegularSeal sealReplayRead _transportLocalName
    modulusUnary streamUnary regularUnary replayUnary realReadPkg
  have dyadicUnary : UnaryHistory dyadic :=
    unary_cont_closed modulusUnary streamUnary modulusStreamDyadic
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed dyadicUnary regularUnary dyadicRegularSeal
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed realSealUnary replayUnary sealReplayRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row modulus ∨ hsame row stream ∨ hsame row dyadic ∨
              hsame row regular ∨ hsame row realSeal ∨ hsame row replay ∨
                hsame row realRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle realRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro realRead ⟨hsame_refl realRead, realReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, realReadPkg⟩
  }
  exact ⟨cert, dyadicUnary, realSealUnary, realReadUnary⟩

end BEDC.Derived.FastCauchyCompletionUp
