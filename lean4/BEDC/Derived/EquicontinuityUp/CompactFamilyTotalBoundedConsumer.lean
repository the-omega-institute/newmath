import BEDC.Derived.EquicontinuityUp.ArzelaAscoliConsumerRoute

namespace BEDC.Derived.EquicontinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EquicontinuityCompactFamilyTotalBoundedConsumer [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead modulusRead finiteNetRead arzelaRead
      totalBoundedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg →
      UnaryHistory M →
        UnaryHistory T →
          UnaryHistory R →
            UnaryHistory P →
              Cont handoffRead M modulusRead →
                Cont modulusRead T finiteNetRead →
                  Cont finiteNetRead R arzelaRead →
                    Cont arzelaRead P totalBoundedRead →
                      PkgSig bundle totalBoundedRead pkg →
                        SemanticNameCert
                            (fun row : BHist =>
                              hsame row totalBoundedRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row K ∨ hsame row F ∨ hsame row eps ∨
                                hsame row rho ∨ hsame row M ∨ hsame row T ∨
                                  hsame row R ∨ hsame row P ∨
                                    hsame row totalBoundedRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ PkgSig bundle totalBoundedRead pkg)
                            hsame ∧
                          UnaryHistory totalBoundedRead := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier unaryM unaryT unaryR unaryP modulusRoute finiteNetRoute arzelaRoute
    totalBoundedRoute totalBoundedPkg
  obtain ⟨_radiusUnary, handoffUnary, _radiusRoute, _handoffRoute, _pkgP, _pkgN⟩ :=
    EquicontinuityCarrier_shared_radius_stability carrier
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed handoffUnary unaryM modulusRoute
  have finiteNetUnary : UnaryHistory finiteNetRead :=
    unary_cont_closed modulusUnary unaryT finiteNetRoute
  have arzelaUnary : UnaryHistory arzelaRead :=
    unary_cont_closed finiteNetUnary unaryR arzelaRoute
  have totalBoundedUnary : UnaryHistory totalBoundedRead :=
    unary_cont_closed arzelaUnary unaryP totalBoundedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row totalBoundedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row eps ∨ hsame row rho ∨
              hsame row M ∨ hsame row T ∨ hsame row R ∨ hsame row P ∨
                hsame row totalBoundedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle totalBoundedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro totalBoundedRead
          ⟨hsame_refl totalBoundedRead, totalBoundedUnary⟩
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
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, totalBoundedPkg⟩
  }
  exact ⟨cert, totalBoundedUnary⟩

end BEDC.Derived.EquicontinuityUp
