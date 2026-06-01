import BEDC.Derived.DecimalExpansionUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.DecimalExpansionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DecimalExpansionRealSealNonescape [AskSetup] [PackageSetup]
    {D W V Q R E H C P N prefixRead placeRead dyadicRead regseqRead realSeal sealedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory D →
      UnaryHistory W →
        UnaryHistory V →
          UnaryHistory Q →
            UnaryHistory R →
              UnaryHistory E →
                UnaryHistory H →
                  Cont D W prefixRead →
                    Cont prefixRead V placeRead →
                      Cont placeRead Q dyadicRead →
                        Cont dyadicRead R regseqRead →
                          Cont regseqRead E realSeal →
                            Cont realSeal H sealedRead →
                              PkgSig bundle P pkg →
                                PkgSig bundle N pkg →
                                  SemanticNameCert
                                      (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row prefixRead ∨ hsame row placeRead ∨
                                          hsame row dyadicRead ∨ hsame row regseqRead ∨
                                            hsame row realSeal ∨ hsame row sealedRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont regseqRead E realSeal ∧
                                          Cont realSeal H sealedRead ∧ PkgSig bundle P pkg ∧
                                            PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory prefixRead ∧ UnaryHistory placeRead ∧
                                      UnaryHistory dyadicRead ∧ UnaryHistory regseqRead ∧
                                        UnaryHistory realSeal ∧ UnaryHistory sealedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro dUnary wUnary vUnary qUnary rUnary eUnary hUnary digitWindow prefixPlace
    placeDyadic dyadicRegSeq regSeqSeal sealTransport provenancePkg namePkg
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed dUnary wUnary digitWindow
  have placeUnary : UnaryHistory placeRead :=
    unary_cont_closed prefixUnary vUnary prefixPlace
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed placeUnary qUnary placeDyadic
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed dyadicUnary rUnary dyadicRegSeq
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regseqUnary eUnary regSeqSeal
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed realSealUnary hUnary sealTransport
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row prefixRead ∨ hsame row placeRead ∨ hsame row dyadicRead ∨
              hsame row regseqRead ∨ hsame row realSeal ∨ hsame row sealedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont regseqRead E realSeal ∧ Cont realSeal H sealedRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sealedRead ⟨hsame_refl sealedRead, sealedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, regSeqSeal, sealTransport, provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, prefixUnary, placeUnary, dyadicUnary, regseqUnary, realSealUnary,
      sealedUnary⟩

end BEDC.Derived.DecimalExpansionUp
