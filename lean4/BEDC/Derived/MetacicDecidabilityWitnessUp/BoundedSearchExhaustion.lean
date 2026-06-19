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

theorem MetacicDecidabilityWitness_bounded_search_exhaustion [AskSetup] [PackageSetup]
    {typing sameTerm bounded finished refusal _transport _route provenance name checkerRead
      conversionRead normalRead exhaustedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory typing ->
      UnaryHistory sameTerm ->
        UnaryHistory bounded ->
          UnaryHistory finished ->
            UnaryHistory refusal ->
              Cont typing sameTerm checkerRead ->
                Cont bounded finished conversionRead ->
                  Cont checkerRead conversionRead normalRead ->
                    Cont normalRead refusal exhaustedRead ->
                      PkgSig bundle provenance pkg ->
                        PkgSig bundle name pkg ->
                          PkgSig bundle exhaustedRead pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row exhaustedRead ∧
                                  UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row typing ∨ hsame row sameTerm ∨
                                    hsame row bounded ∨ hsame row finished ∨
                                      hsame row normalRead ∨ hsame row exhaustedRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧
                                    Cont typing sameTerm checkerRead ∧
                                      Cont bounded finished conversionRead ∧
                                        Cont checkerRead conversionRead normalRead ∧
                                          Cont normalRead refusal exhaustedRead ∧
                                            PkgSig bundle provenance pkg ∧
                                              PkgSig bundle name pkg)
                                hsame ∧
                              UnaryHistory checkerRead ∧ UnaryHistory conversionRead ∧
                                UnaryHistory normalRead ∧ UnaryHistory exhaustedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro typingUnary sameTermUnary boundedUnary finishedUnary refusalUnary checkerRoute
    conversionRoute normalRoute exhaustedRoute provenancePkg namePkg _exhaustedPkg
  have checkerUnary : UnaryHistory checkerRead :=
    unary_cont_closed typingUnary sameTermUnary checkerRoute
  have conversionUnary : UnaryHistory conversionRead :=
    unary_cont_closed boundedUnary finishedUnary conversionRoute
  have normalUnary : UnaryHistory normalRead :=
    unary_cont_closed checkerUnary conversionUnary normalRoute
  have exhaustedUnary : UnaryHistory exhaustedRead :=
    unary_cont_closed normalUnary refusalUnary exhaustedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exhaustedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typing ∨ hsame row sameTerm ∨ hsame row bounded ∨
              hsame row finished ∨ hsame row normalRead ∨ hsame row exhaustedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont typing sameTerm checkerRead ∧
              Cont bounded finished conversionRead ∧
                Cont checkerRead conversionRead normalRead ∧
                  Cont normalRead refusal exhaustedRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro exhaustedRead ⟨hsame_refl exhaustedRead, exhaustedUnary⟩
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
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, checkerRoute, conversionRoute, normalRoute, exhaustedRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, checkerUnary, conversionUnary, normalUnary, exhaustedUnary⟩

end BEDC.Derived.MetacicDecidabilityWitnessUp
