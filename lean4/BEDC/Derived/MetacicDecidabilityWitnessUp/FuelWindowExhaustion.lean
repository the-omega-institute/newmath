import BEDC.Derived.MetacicDecidabilityWitnessUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetacicDecidabilityWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicDecidabilityWitnessFuelWindowExhaustion [AskSetup] [PackageSetup]
    {typing sameTerm bounded finished refusal provenance localName diamondRow checkerRead
      conversionRead normalRead diamondRead exhaustedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory typing →
      UnaryHistory sameTerm →
        UnaryHistory bounded →
          UnaryHistory finished →
            UnaryHistory refusal →
              UnaryHistory diamondRow →
                Cont typing sameTerm checkerRead →
                  Cont bounded finished conversionRead →
                    Cont checkerRead conversionRead normalRead →
                      Cont normalRead diamondRow diamondRead →
                        Cont diamondRead refusal exhaustedRead →
                          PkgSig bundle provenance pkg →
                            PkgSig bundle localName pkg →
                              SemanticNameCert
                                  (fun row : BHist =>
                                    hsame row exhaustedRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row typing ∨ hsame row sameTerm ∨
                                      hsame row bounded ∨ hsame row finished ∨
                                        hsame row refusal ∨ hsame row diamondRow ∨
                                          hsame row normalRead ∨ hsame row diamondRead ∨
                                            hsame row exhaustedRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧
                                      Cont typing sameTerm checkerRead ∧
                                        Cont bounded finished conversionRead ∧
                                          Cont checkerRead conversionRead normalRead ∧
                                            Cont normalRead diamondRow diamondRead ∧
                                              Cont diamondRead refusal exhaustedRead ∧
                                                PkgSig bundle provenance pkg ∧
                                                  PkgSig bundle localName pkg)
                                  hsame ∧
                                UnaryHistory checkerRead ∧
                                  UnaryHistory conversionRead ∧ UnaryHistory normalRead ∧
                                    UnaryHistory diamondRead ∧
                                      UnaryHistory exhaustedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro typingUnary sameTermUnary boundedUnary finishedUnary refusalUnary diamondUnary
    checkerRoute conversionRoute normalRoute diamondRoute exhaustedRoute provenancePkg
    localNamePkg
  have checkerUnary : UnaryHistory checkerRead :=
    unary_cont_closed typingUnary sameTermUnary checkerRoute
  have conversionUnary : UnaryHistory conversionRead :=
    unary_cont_closed boundedUnary finishedUnary conversionRoute
  have normalUnary : UnaryHistory normalRead :=
    unary_cont_closed checkerUnary conversionUnary normalRoute
  have diamondReadUnary : UnaryHistory diamondRead :=
    unary_cont_closed normalUnary diamondUnary diamondRoute
  have exhaustedUnary : UnaryHistory exhaustedRead :=
    unary_cont_closed diamondReadUnary refusalUnary exhaustedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exhaustedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typing ∨ hsame row sameTerm ∨ hsame row bounded ∨
              hsame row finished ∨ hsame row refusal ∨ hsame row diamondRow ∨
                hsame row normalRead ∨ hsame row diamondRead ∨ hsame row exhaustedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont typing sameTerm checkerRead ∧
              Cont bounded finished conversionRead ∧
                Cont checkerRead conversionRead normalRead ∧
                  Cont normalRead diamondRow diamondRead ∧
                    Cont diamondRead refusal exhaustedRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exhaustedRead ⟨hsame_refl exhaustedRead, exhaustedUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, checkerRoute, conversionRoute, normalRoute, diamondRoute,
          exhaustedRoute, provenancePkg, localNamePkg⟩
  }
  exact
    ⟨cert, checkerUnary, conversionUnary, normalUnary, diamondReadUnary,
      exhaustedUnary⟩

end BEDC.Derived.MetacicDecidabilityWitnessUp
