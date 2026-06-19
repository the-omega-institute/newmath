import BEDC.Derived.DcpoUp
import BEDC.FKernel.Package

namespace BEDC.Derived.DcpoUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DcpoCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {O I W S M F Q _L _H _C P _N directedRead supremumRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory O ->
      UnaryHistory I ->
        UnaryHistory W ->
          UnaryHistory M ->
            UnaryHistory F ->
              Cont O I directedRead ->
                Cont directedRead W supremumRead ->
                  Cont M F completionRead ->
                    PkgSig bundle P pkg ->
                      SemanticNameCert
                            (fun row : BHist =>
                              (hsame row supremumRead ∨ hsame row completionRead) ∧
                                UnaryHistory row)
                            (fun row : BHist =>
                              hsame row O ∨ hsame row I ∨ hsame row W ∨ hsame row S ∨
                                hsame row M ∨ hsame row F ∨ hsame row Q ∨
                                  hsame row supremumRead ∨ hsame row completionRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont O I directedRead ∧
                                Cont directedRead W supremumRead ∧
                                  Cont M F completionRead ∧ PkgSig bundle P pkg)
                            hsame ∧
                          UnaryHistory directedRead ∧ UnaryHistory supremumRead ∧
                            UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro unaryO unaryI unaryW unaryM unaryF directedRoute supremumRoute completionRoute pkgSig
  have directedUnary : UnaryHistory directedRead :=
    unary_cont_closed unaryO unaryI directedRoute
  have supremumUnary : UnaryHistory supremumRead :=
    unary_cont_closed directedUnary unaryW supremumRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed unaryM unaryF completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row supremumRead ∨ hsame row completionRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row O ∨ hsame row I ∨ hsame row W ∨ hsame row S ∨
              hsame row M ∨ hsame row F ∨ hsame row Q ∨ hsame row supremumRead ∨
                hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont O I directedRead ∧
              Cont directedRead W supremumRead ∧ Cont M F completionRead ∧
                PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro supremumRead
          ⟨Or.inl (hsame_refl supremumRead), supremumUnary⟩
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameSupremum =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl sameSupremum)))))))
      | inr sameCompletion =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr sameCompletion)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, directedRoute, supremumRoute, completionRoute, pkgSig⟩
  }
  exact ⟨cert, directedUnary, supremumUnary, completionUnary⟩

end BEDC.Derived.DcpoUp
