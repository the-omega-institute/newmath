import BEDC.Derived.LocallyCompactUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocallyCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.LocallyCompactUp.TasteGate

theorem LocallyCompactLocalCompactNeighborhoodObligations [AskSetup] [PackageSetup]
    {X x r B K A H C P N compactRead locatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    locallyCompactFields (LocallyCompactUp.mk X x r B K A H C P N) =
        [X, x, r, B, K, A, H, C, P, N] →
      UnaryHistory B →
        UnaryHistory K →
          UnaryHistory A →
            Cont B K compactRead →
              Cont compactRead A locatedRead →
                PkgSig bundle P pkg →
                  PkgSig bundle N pkg →
                    SemanticNameCert
                          (fun row : BHist => hsame row locatedRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row X ∨ hsame row x ∨ hsame row r ∨ hsame row B ∨
                              hsame row K ∨ hsame row A ∨ hsame row H ∨ hsame row C ∨
                                hsame row P ∨ hsame row N ∨ hsame row compactRead ∨
                                  hsame row locatedRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont B K compactRead ∧
                              Cont compactRead A locatedRead ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle N pkg)
                          hsame ∧
                        UnaryHistory compactRead ∧ UnaryHistory locatedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro fieldsExact unaryB unaryK unaryA compactRoute locatedRoute provenancePkg localNamePkg
  cases fieldsExact
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed unaryB unaryK compactRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed compactUnary unaryA locatedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row locatedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row x ∨ hsame row r ∨ hsame row B ∨ hsame row K ∨
              hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row compactRead ∨ hsame row locatedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B K compactRead ∧
              Cont compactRead A locatedRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro locatedRead ⟨hsame_refl locatedRead, locatedUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, compactRoute, locatedRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, compactUnary, locatedUnary⟩

end BEDC.Derived.LocallyCompactUp
