import BEDC.Derived.EgorovUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EgorovUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem Egorov_finite_window_uniformity [AskSetup] [PackageSetup]
    {M Omega F X S R A W U L H C P N windowRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EgorovCarrier M Omega F X S R A W U L H C P N bundle pkg →
      Cont W R windowRead →
        Cont windowRead U uniformRead →
          SemanticNameCert
              (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row W ∨ hsame row R ∨ hsame row U ∨ hsame row A ∨
                  hsame row L ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                    hsame row N ∨ hsame row windowRead ∨ hsame row uniformRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont W R windowRead ∧ Cont windowRead U uniformRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
              hsame ∧
            UnaryHistory uniformRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier windowRoute uniformRoute
  obtain ⟨_packet, _unaryM, _unaryOmega, _unaryF, _unaryX, _unaryS, unaryR, _unaryA,
    unaryW, unaryU, _unaryL, _unaryH, _unaryC, _unaryP, _unaryN, pkgP, pkgN⟩ :=
    carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryW unaryR windowRoute
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed windowUnary unaryU uniformRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row R ∨ hsame row U ∨ hsame row A ∨
              hsame row L ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row windowRead ∨ hsame row uniformRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R windowRead ∧ Cont windowRead U uniformRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro uniformRead ⟨hsame_refl uniformRead, uniformUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, windowRoute, uniformRoute, pkgP, pkgN⟩
  }
  exact ⟨cert, uniformUnary⟩

end BEDC.Derived.EgorovUp
