import SyracuseLaw
import Erdos1135.Tao.Syracuse.Syrac
import Erdos1135.Tao.Section6.ModulusProjection

/-! Identification of the paper's probability law with the law used by the
mixing estimates. The two recursions sample the independent variables in
opposite orders; commutation of PMF binds proves equality at every depth.
-/
namespace SyracuseReport

theorem letterLaw_eq_geom2PNat : letterLaw = Erdos1135.Tao.geom2PNat := rfl

theorem affineStep_eq_syracStep (n : ℕ) (a : ℕ+) (z : ZMod (3 ^ n)) :
    affineStep n a z = Erdos1135.Tao.syracStep n z a := rfl

theorem syracuseLaw_eq_syracPMF (n : ℕ) :
    syracuseLaw n = Erdos1135.Tao.syracPMF n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [syracuseLaw, Erdos1135.Tao.syracPMF, ih, letterLaw_eq_geom2PNat]
    change
      (Erdos1135.Tao.geom2PNat.bind fun a =>
        (Erdos1135.Tao.syracPMF n).bind fun z =>
          PMF.pure (affineStep n a z)) =
      (Erdos1135.Tao.syracPMF n).bind fun z =>
        Erdos1135.Tao.geom2PNat.bind fun a =>
          PMF.pure (affineStep n a z)
    exact PMF.bind_comm _ _ _

theorem residueProjection_eq_reference {q t : ℕ} (h : t ≤ q) :
    residueProjection h = Erdos1135.Tao.taoZModThreeProjection h := rfl

end SyracuseReport
