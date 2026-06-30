import BEDC.Derived.TerminationRefusalBoundaryUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TerminationRefusalBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TerminationRefusalBoundaryCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {S I T F U H C P N traceRead refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S →
      UnaryHistory I →
        UnaryHistory T →
          UnaryHistory F →
            UnaryHistory U →
              UnaryHistory H →
                Cont T F traceRead →
                  Cont U H refusalRead →
                    PkgSig bundle P pkg →
                      SemanticNameCert
                          (fun row : BHist =>
                            (hsame row traceRead ∨ hsame row refusalRead) ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row S ∨ hsame row I ∨ hsame row T ∨ hsame row F ∨
                              hsame row U ∨ hsame row traceRead ∨ hsame row refusalRead)
                          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg)
                          hsame ∧
                        UnaryHistory traceRead ∧ UnaryHistory refusalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro _sUnary _iUnary tUnary fUnary uUnary hUnary traceRoute refusalRoute provenancePkg
  have traceUnary : UnaryHistory traceRead :=
    unary_cont_closed tUnary fUnary traceRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed uUnary hUnary refusalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row traceRead ∨ hsame row refusalRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row I ∨ hsame row T ∨ hsame row F ∨ hsame row U ∨
              hsame row traceRead ∨ hsame row refusalRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro traceRead ⟨Or.inl (hsame_refl traceRead),
          traceUnary⟩
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
          constructor
          · cases source.left with
            | inl sameTrace =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameTrace)
            | inr sameRefusal =>
                exact Or.inr (hsame_trans (hsame_symm sameRows) sameRefusal)
          · exact unary_transport source.right sameRows
      }
      pattern_sound := by
        intro _row source
        cases source.left with
        | inl sameTrace =>
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameTrace)))))
        | inr sameRefusal =>
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameRefusal)))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, provenancePkg⟩
    }
  exact ⟨cert, traceUnary, refusalUnary⟩

theorem TerminationRefusalBoundaryCarrier_nonescape [AskSetup] [PackageSetup]
    {S I T F U H C P N traceRead refusalRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont T F traceRead →
      Cont U H refusalRead →
        Cont C P namedRead →
          PkgSig bundle P pkg →
            PkgSig bundle N pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row traceRead ∨ hsame row refusalRead ∨ hsame row namedRead)
                  (fun row : BHist =>
                    hsame row S ∨ hsame row I ∨ hsame row T ∨ hsame row F ∨
                      hsame row U ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                        hsame row N ∨ hsame row traceRead ∨ hsame row refusalRead ∨
                          hsame row namedRead)
                  (fun _row : BHist =>
                    Cont T F traceRead ∧ Cont U H refusalRead ∧ Cont C P namedRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                  hsame ∧
                Cont T F traceRead ∧ Cont U H refusalRead ∧ Cont C P namedRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro traceRoute refusalRoute namedRoute provenancePkg localNamePkg
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row traceRead ∨ hsame row refusalRead ∨ hsame row namedRead)
          (fun row : BHist =>
            hsame row S ∨ hsame row I ∨ hsame row T ∨ hsame row F ∨ hsame row U ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row traceRead ∨ hsame row refusalRead ∨ hsame row namedRead)
          (fun _row : BHist =>
            Cont T F traceRead ∧ Cont U H refusalRead ∧ Cont C P namedRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro traceRead (Or.inl (hsame_refl traceRead))
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
          cases source with
          | inl sameTrace =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameTrace)
          | inr rest =>
              cases rest with
              | inl sameRefusal =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameRefusal))
              | inr sameNamed =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameNamed))
      }
      pattern_sound := by
        intro _row source
        cases source with
        | inl sameTrace =>
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inr (Or.inl sameTrace)))))))))
        | inr rest =>
            cases rest with
            | inl sameRefusal =>
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inr (Or.inl sameRefusal))))))))))
            | inr sameNamed =>
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inr (Or.inr sameNamed))))))))))
      ledger_sound := by
        intro _row _source
        exact ⟨traceRoute, refusalRoute, namedRoute, provenancePkg, localNamePkg⟩
    }
  exact
    ⟨cert, traceRoute, refusalRoute, namedRoute, provenancePkg, localNamePkg⟩

end BEDC.Derived.TerminationRefusalBoundaryUp
