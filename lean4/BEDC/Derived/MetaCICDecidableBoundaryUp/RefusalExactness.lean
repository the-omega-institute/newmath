import BEDC.Derived.MetaCICDecidableBoundaryUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.MetaCICDecidableBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICDecidableBoundaryRefusalExactness [AskSetup] [PackageSetup]
    {checker structural boundedNormal finished refusal transport _replay provenance
      localName boundedRead refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory checker →
      UnaryHistory structural →
        UnaryHistory finished →
          UnaryHistory refusal →
            UnaryHistory transport →
              Cont checker structural boundedNormal →
                Cont boundedNormal finished boundedRead →
                  Cont refusal transport refusalRead →
                    PkgSig bundle provenance pkg →
                      PkgSig bundle localName pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row refusal ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row refusal ∨ hsame row boundedNormal ∨
                                hsame row boundedRead ∨ hsame row refusalRead ∨
                                  hsame row localName)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont checker structural boundedNormal ∧
                                Cont boundedNormal finished boundedRead ∧
                                  Cont refusal transport refusalRead ∧
                                    PkgSig bundle localName pkg)
                            hsame ∧
                          UnaryHistory boundedNormal ∧ UnaryHistory boundedRead ∧
                            UnaryHistory refusalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro checkerUnary structuralUnary finishedUnary refusalUnary transportUnary
  intro checkerStructuralBounded boundedFinishedRead refusalTransportRead _provenancePkg localPkg
  have boundedNormalUnary : UnaryHistory boundedNormal :=
    unary_cont_closed checkerUnary structuralUnary checkerStructuralBounded
  have boundedReadUnary : UnaryHistory boundedRead :=
    unary_cont_closed boundedNormalUnary finishedUnary boundedFinishedRead
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed refusalUnary transportUnary refusalTransportRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row refusal ∨ hsame row boundedNormal ∨ hsame row boundedRead ∨
              hsame row refusalRead ∨ hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont checker structural boundedNormal ∧
              Cont boundedNormal finished boundedRead ∧ Cont refusal transport refusalRead ∧
                PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusal ⟨hsame_refl refusal, refusalUnary⟩
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
        intro row other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inl source.left
    ledger_sound := by
      intro row source
      exact
        ⟨source.right, checkerStructuralBounded, boundedFinishedRead, refusalTransportRead,
          localPkg⟩
  }
  exact ⟨cert, boundedNormalUnary, boundedReadUnary, refusalReadUnary⟩

end BEDC.Derived.MetaCICDecidableBoundaryUp
