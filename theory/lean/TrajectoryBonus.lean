import ExtendedLogBounds
import AgentUCTPaper.TreeAllocation
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
noncomputable section
namespace AgentUCT32MConcrete
open AgentUCTPaper AgentUCTRealIndex
theorem trajectory_bonus_4_1 : ((44402267/25000000):ℝ) ≤ treeBonus (7/5) 4 1 ∧
    treeBonus (7/5) 4 1 ≤ ((88804541/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((16094379/10000000)) ((804719/500000)) ((6343181/5000000)) ((12686363/10000000)) 4 1
    (by norm_num) (by norm_num)
    log_5_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_5_1 : ((93699627/50000000):ℝ) ≤ treeBonus (7/5) 5 1 ∧
    treeBonus (7/5) 5 1 ≤ ((93699641/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((8958797/5000000)) ((3583519/2000000)) ((13385661/10000000)) ((13385663/10000000)) 5 1
    (by norm_num) (by norm_num)
    log_6_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_5_2 : ((16563911/12500000):ℝ) ≤ treeBonus (7/5) 5 2 ∧
    treeBonus (7/5) 5 2 ≤ ((66255651/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((8958797/5000000)) ((3583519/2000000)) ((2366273/2500000)) ((9465093/10000000)) 5 2
    (by norm_num) (by norm_num)
    log_6_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_6_1 : ((24411779/12500000):ℝ) ≤ treeBonus (7/5) 6 1 ∧
    treeBonus (7/5) 6 1 ≤ ((97647123/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((19459101/10000000)) ((9729551/5000000)) ((3487397/2500000)) ((13949589/10000000)) 6 1
    (by norm_num) (by norm_num)
    log_7_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_6_2 : ((8630867/6250000):ℝ) ≤ treeBonus (7/5) 6 2 ∧
    treeBonus (7/5) 6 2 ≤ ((69046943/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((19459101/10000000)) ((9729551/5000000)) ((1232981/1250000)) ((9863849/10000000)) 6 2
    (by norm_num) (by norm_num)
    log_7_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_7_1 : ((25235469/12500000):ℝ) ≤ treeBonus (7/5) 7 1 ∧
    treeBonus (7/5) 7 1 ≤ ((10094189/5000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((4158883/2000000)) ((1299651/625000)) ((3605067/2500000)) ((1442027/1000000)) 7 1
    (by norm_num) (by norm_num)
    log_8_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_7_2 : ((71376683/50000000):ℝ) ≤ treeBonus (7/5) 7 2 ∧
    treeBonus (7/5) 7 2 ≤ ((71376697/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((4158883/2000000)) ((1299651/625000)) ((10196669/10000000)) ((10196671/10000000)) 7 2
    (by norm_num) (by norm_num)
    log_8_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_8_1 : ((103761259/50000000):ℝ) ≤ treeBonus (7/5) 8 1 ∧
    treeBonus (7/5) 8 1 ≤ ((103761273/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((4394449/2000000)) ((21972247/10000000)) ((14823037/10000000)) ((14823039/10000000)) 8 1
    (by norm_num) (by norm_num)
    log_9_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_8_2 : ((7337029/5000000):ℝ) ≤ treeBonus (7/5) 8 2 ∧
    treeBonus (7/5) 8 2 ≤ ((1146411/781250):ℝ) := by
  have h := uct_bonus_interval (7/5) ((4394449/2000000)) ((21972247/10000000)) ((1048147/1000000)) ((163773/156250)) 8 2
    (by norm_num) (by norm_num)
    log_9_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_8_3 : ((14976647/12500000):ℝ) ≤ treeBonus (7/5) 8 3 ∧
    treeBonus (7/5) 8 3 ≤ ((29953301/25000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((4394449/2000000)) ((21972247/10000000)) ((2139521/2500000)) ((4279043/5000000)) 8 3
    (by norm_num) (by norm_num)
    log_9_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_9_2 : ((75108803/50000000):ℝ) ≤ treeBonus (7/5) 9 2 ∧
    treeBonus (7/5) 9 2 ≤ ((75108817/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((460517/200000)) ((23025851/10000000)) ((10729829/10000000)) ((10729831/10000000)) 9 2
    (by norm_num) (by norm_num)
    log_10_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_9_3 : ((61326083/50000000):ℝ) ≤ treeBonus (7/5) 9 3 ∧
    treeBonus (7/5) 9 3 ≤ ((6132609/5000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((460517/200000)) ((23025851/10000000)) ((8760869/10000000)) ((876087/1000000)) 9 3
    (by norm_num) (by norm_num)
    log_10_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_9_4 : ((10621989/10000000):ℝ) ≤ treeBonus (7/5) 9 4 ∧
    treeBonus (7/5) 9 4 ≤ ((829843/781250):ℝ) := by
  have h := uct_bonus_interval (7/5) ((460517/200000)) ((23025851/10000000)) ((1517427/2000000)) ((118549/156250)) 9 4
    (by norm_num) (by norm_num)
    log_10_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_10_1 : ((54197983/25000000):ℝ) ≤ treeBonus (7/5) 10 1 ∧
    treeBonus (7/5) 10 1 ≤ ((5419799/2500000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((2997369/1250000)) ((23978953/10000000)) ((7742569/5000000)) ((774257/500000)) 10 1
    (by norm_num) (by norm_num)
    log_11_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_10_2 : ((38323761/25000000):ℝ) ≤ treeBonus (7/5) 10 2 ∧
    treeBonus (7/5) 10 2 ≤ ((76647529/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((2997369/1250000)) ((23978953/10000000)) ((5474823/5000000)) ((10949647/10000000)) 10 2
    (by norm_num) (by norm_num)
    log_11_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_10_3 : ((15645609/12500000):ℝ) ≤ treeBonus (7/5) 10 3 ∧
    treeBonus (7/5) 10 3 ≤ ((1251649/1000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((2997369/1250000)) ((23978953/10000000)) ((2235087/2500000)) ((178807/200000)) 10 3
    (by norm_num) (by norm_num)
    log_11_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_10_4 : ((54197983/50000000):ℝ) ≤ treeBonus (7/5) 10 4 ∧
    treeBonus (7/5) 10 4 ≤ ((5419799/5000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((2997369/1250000)) ((23978953/10000000)) ((7742569/10000000)) ((774257/1000000)) 10 4
    (by norm_num) (by norm_num)
    log_11_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_11_1 : ((55172551/25000000):ℝ) ≤ treeBonus (7/5) 11 1 ∧
    treeBonus (7/5) 11 1 ≤ ((110345109/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((12424533/5000000)) ((24849067/10000000)) ((7881793/5000000)) ((15763587/10000000)) 11 1
    (by norm_num) (by norm_num)
    log_12_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_11_2 : ((39012883/25000000):ℝ) ≤ treeBonus (7/5) 11 2 ∧
    treeBonus (7/5) 11 2 ≤ ((3901289/2500000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((12424533/5000000)) ((24849067/10000000)) ((5573269/5000000)) ((557327/500000)) 11 2
    (by norm_num) (by norm_num)
    log_12_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_11_3 : ((6370777/5000000):ℝ) ≤ treeBonus (7/5) 11 3 ∧
    treeBonus (7/5) 11 3 ≤ ((7963473/6250000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((12424533/5000000)) ((24849067/10000000)) ((910111/1000000)) ((1137639/1250000)) 11 3
    (by norm_num) (by norm_num)
    log_12_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_11_4 : ((55172551/50000000):ℝ) ≤ treeBonus (7/5) 11 4 ∧
    treeBonus (7/5) 11 4 ≤ ((27586279/25000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((12424533/5000000)) ((24849067/10000000)) ((7881793/10000000)) ((3940897/5000000)) 11 4
    (by norm_num) (by norm_num)
    log_12_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_12_1 : ((112108213/50000000):ℝ) ≤ treeBonus (7/5) 12 1 ∧
    treeBonus (7/5) 12 1 ≤ ((5605411/2500000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((25649493/10000000)) ((12824747/5000000)) ((16015459/10000000)) ((800773/500000)) 12 1
    (by norm_num) (by norm_num)
    log_13_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_12_2 : ((79272473/50000000):ℝ) ≤ treeBonus (7/5) 12 2 ∧
    treeBonus (7/5) 12 2 ≤ ((495453/312500):ℝ) := by
  have h := uct_bonus_interval (7/5) ((25649493/10000000)) ((12824747/5000000)) ((11324639/10000000)) ((70779/62500)) 12 2
    (by norm_num) (by norm_num)
    log_13_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_12_3 : ((64725703/50000000):ℝ) ≤ treeBonus (7/5) 12 3 ∧
    treeBonus (7/5) 12 3 ≤ ((6472571/5000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((25649493/10000000)) ((12824747/5000000)) ((9246529/10000000)) ((924653/1000000)) 12 3
    (by norm_num) (by norm_num)
    log_13_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_12_4 : ((56054103/50000000):ℝ) ≤ treeBonus (7/5) 12 4 ∧
    treeBonus (7/5) 12 4 ≤ ((5605411/5000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((25649493/10000000)) ((12824747/5000000)) ((8007729/10000000)) ((800773/1000000)) 12 4
    (by norm_num) (by norm_num)
    log_13_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_12_5 : ((50136317/50000000):ℝ) ≤ treeBonus (7/5) 12 5 ∧
    treeBonus (7/5) 12 5 ≤ ((12534081/12500000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((25649493/10000000)) ((12824747/5000000)) ((7162331/10000000)) ((1790583/2500000)) 12 5
    (by norm_num) (by norm_num)
    log_13_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_13_1 : ((4548649/2000000):ℝ) ≤ treeBonus (7/5) 13 1 ∧
    treeBonus (7/5) 13 1 ≤ ((14214529/6250000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((26390573/10000000)) ((13195287/5000000)) ((649807/400000)) ((2030647/1250000)) 13 1
    (by norm_num) (by norm_num)
    log_14_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_13_2 : ((80409511/50000000):ℝ) ≤ treeBonus (7/5) 13 2 ∧
    treeBonus (7/5) 13 2 ≤ ((3216381/2000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((26390573/10000000)) ((13195287/5000000)) ((11487073/10000000)) ((459483/400000)) 13 2
    (by norm_num) (by norm_num)
    log_14_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_13_3 : ((16413523/12500000):ℝ) ≤ treeBonus (7/5) 13 3 ∧
    treeBonus (7/5) 13 3 ≤ ((65654099/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((26390573/10000000)) ((13195287/5000000)) ((2344789/2500000)) ((9379157/10000000)) 13 3
    (by norm_num) (by norm_num)
    log_14_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_13_4 : ((56858109/50000000):ℝ) ≤ treeBonus (7/5) 13 4 ∧
    treeBonus (7/5) 13 4 ≤ ((14214529/12500000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((26390573/10000000)) ((13195287/5000000)) ((8122587/10000000)) ((2030647/2500000)) 13 4
    (by norm_num) (by norm_num)
    log_14_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_13_5 : ((50855441/50000000):ℝ) ≤ treeBonus (7/5) 13 5 ∧
    treeBonus (7/5) 13 5 ≤ ((6356931/6250000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((26390573/10000000)) ((13195287/5000000)) ((7265063/10000000)) ((908133/1250000)) 13 5
    (by norm_num) (by norm_num)
    log_14_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_14_1 : ((57596539/25000000):ℝ) ≤ treeBonus (7/5) 14 1 ∧
    treeBonus (7/5) 14 1 ≤ ((23038617/10000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((13540251/5000000)) ((27080503/10000000)) ((8228077/5000000)) ((3291231/2000000)) 14 1
    (by norm_num) (by norm_num)
    log_15_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_14_2 : ((40726903/25000000):ℝ) ≤ treeBonus (7/5) 14 2 ∧
    treeBonus (7/5) 14 2 ≤ ((81453813/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((13540251/5000000)) ((27080503/10000000)) ((5818129/5000000)) ((11636259/10000000)) 14 2
    (by norm_num) (by norm_num)
    log_15_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_14_4 : ((57596539/50000000):ℝ) ≤ treeBonus (7/5) 14 4 ∧
    treeBonus (7/5) 14 4 ≤ ((28798273/25000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((13540251/5000000)) ((27080503/10000000)) ((8228077/10000000)) ((4114039/5000000)) 14 4
    (by norm_num) (by norm_num)
    log_15_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_14_5 : ((6439489/6250000):ℝ) ≤ treeBonus (7/5) 14 5 ∧
    treeBonus (7/5) 14 5 ≤ ((51515919/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((13540251/5000000)) ((27080503/10000000)) ((919927/1250000)) ((7359417/10000000)) 14 5
    (by norm_num) (by norm_num)
    log_15_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_15_1 : ((29139411/12500000):ℝ) ≤ treeBonus (7/5) 15 1 ∧
    treeBonus (7/5) 15 1 ≤ ((116557651/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((27725887/10000000)) ((433217/156250)) ((4162773/2500000)) ((16651093/10000000)) 15 1
    (by norm_num) (by norm_num)
    log_16_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_15_2 : ((824187/500000):ℝ) ≤ treeBonus (7/5) 15 2 ∧
    treeBonus (7/5) 15 2 ≤ ((82418707/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((27725887/10000000)) ((433217/156250)) ((117741/100000)) ((11774101/10000000)) 15 2
    (by norm_num) (by norm_num)
    log_16_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_15_4 : ((29139411/25000000):ℝ) ≤ treeBonus (7/5) 15 4 ∧
    treeBonus (7/5) 15 4 ≤ ((58278829/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((27725887/10000000)) ((433217/156250)) ((4162773/5000000)) ((8325547/10000000)) 15 4
    (by norm_num) (by norm_num)
    log_16_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_15_5 : ((26063079/25000000):ℝ) ≤ treeBonus (7/5) 15 5 ∧
    treeBonus (7/5) 15 5 ≤ ((10425233/10000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((27725887/10000000)) ((433217/156250)) ((3723297/5000000)) ((1489319/2000000)) 15 5
    (by norm_num) (by norm_num)
    log_16_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_15_6 : ((47584453/50000000):ℝ) ≤ treeBonus (7/5) 15 6 ∧
    treeBonus (7/5) 15 6 ≤ ((47584467/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((27725887/10000000)) ((433217/156250)) ((6797779/10000000)) ((6797781/10000000)) 15 6
    (by norm_num) (by norm_num)
    log_16_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_16_2 : ((5207181/3125000):ℝ) ≤ treeBonus (7/5) 16 2 ∧
    treeBonus (7/5) 16 2 ≤ ((8331491/5000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((28332131/10000000)) ((3541517/1250000)) ((743883/625000)) ((1190213/1000000)) 16 2
    (by norm_num) (by norm_num)
    log_17_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_16_4 : ((2356501/2000000):ℝ) ≤ treeBonus (7/5) 16 4 ∧
    treeBonus (7/5) 16 4 ≤ ((58912539/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((28332131/10000000)) ((3541517/1250000)) ((336643/400000)) ((8416077/10000000)) 16 4
    (by norm_num) (by norm_num)
    log_17_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_16_5 : ((26346481/25000000):ℝ) ≤ treeBonus (7/5) 16 5 ∧
    treeBonus (7/5) 16 5 ≤ ((3293311/3125000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((28332131/10000000)) ((3541517/1250000)) ((3763783/5000000)) ((470473/625000)) 16 5
    (by norm_num) (by norm_num)
    log_17_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_16_7 : ((8906737/10000000):ℝ) ≤ treeBonus (7/5) 16 7 ∧
    treeBonus (7/5) 16 7 ≤ ((11133423/12500000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((28332131/10000000)) ((3541517/1250000)) ((1272391/2000000)) ((1590489/2500000)) 16 7
    (by norm_num) (by norm_num)
    log_17_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_17_2 : ((21037779/12500000):ℝ) ≤ treeBonus (7/5) 17 2 ∧
    treeBonus (7/5) 17 2 ≤ ((84151123/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((28903717/10000000)) ((28903719/10000000)) ((3005397/2500000)) ((12021589/10000000)) 17 2
    (by norm_num) (by norm_num)
    log_18_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_17_3 : ((13741819/10000000):ℝ) ≤ treeBonus (7/5) 17 3 ∧
    treeBonus (7/5) 17 3 ≤ ((68709109/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((28903717/10000000)) ((28903719/10000000)) ((1963117/2000000)) ((9815587/10000000)) 17 3
    (by norm_num) (by norm_num)
    log_18_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_17_4 : ((29751911/25000000):ℝ) ≤ treeBonus (7/5) 17 4 ∧
    treeBonus (7/5) 17 4 ≤ ((59503829/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((28903717/10000000)) ((28903719/10000000)) ((4250273/5000000)) ((8500547/10000000)) 17 4
    (by norm_num) (by norm_num)
    log_18_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_17_5 : ((665273/625000):ℝ) ≤ treeBonus (7/5) 17 5 ∧
    treeBonus (7/5) 17 5 ≤ ((53221847/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((28903717/10000000)) ((28903719/10000000)) ((95039/125000)) ((7603121/10000000)) 17 5
    (by norm_num) (by norm_num)
    log_18_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_17_6 : ((48584669/50000000):ℝ) ≤ treeBonus (7/5) 17 6 ∧
    treeBonus (7/5) 17 6 ≤ ((12146169/12500000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((28903717/10000000)) ((28903719/10000000)) ((6940667/10000000)) ((1735167/2500000)) 17 6
    (by norm_num) (by norm_num)
    log_18_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_17_7 : ((44980663/50000000):ℝ) ≤ treeBonus (7/5) 17 7 ∧
    treeBonus (7/5) 17 7 ≤ ((4498067/5000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((28903717/10000000)) ((28903719/10000000)) ((6425809/10000000)) ((642581/1000000)) 17 7
    (by norm_num) (by norm_num)
    log_18_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_18_2 : ((16986907/10000000):ℝ) ≤ treeBonus (7/5) 18 2 ∧
    treeBonus (7/5) 18 2 ≤ ((42467271/25000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((29444389/10000000)) ((2944439/1000000)) ((2426701/2000000)) ((6066753/5000000)) 18 2
    (by norm_num) (by norm_num)
    log_19_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_18_3 : ((13869751/10000000):ℝ) ≤ treeBonus (7/5) 18 3 ∧
    treeBonus (7/5) 18 3 ≤ ((34674381/25000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((29444389/10000000)) ((2944439/1000000)) ((1981393/2000000)) ((4953483/5000000)) 18 3
    (by norm_num) (by norm_num)
    log_19_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_18_5 : ((26858657/25000000):ℝ) ≤ treeBonus (7/5) 18 5 ∧
    treeBonus (7/5) 18 5 ≤ ((53717321/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((29444389/10000000)) ((2944439/1000000)) ((3836951/5000000)) ((7673903/10000000)) 18 5
    (by norm_num) (by norm_num)
    log_19_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_18_6 : ((24518487/25000000):ℝ) ≤ treeBonus (7/5) 18 6 ∧
    treeBonus (7/5) 18 6 ≤ ((49036981/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((29444389/10000000)) ((2944439/1000000)) ((3502641/5000000)) ((7005283/10000000)) 18 6
    (by norm_num) (by norm_num)
    log_19_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_18_7 : ((45399417/50000000):ℝ) ≤ treeBonus (7/5) 18 7 ∧
    treeBonus (7/5) 18 7 ≤ ((354683/390625):ℝ) := by
  have h := uct_bonus_interval (7/5) ((29444389/10000000)) ((2944439/1000000)) ((6485631/10000000)) ((50669/78125)) 18 7
    (by norm_num) (by norm_num)
    log_19_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_19_2 : ((42835569/25000000):ℝ) ≤ treeBonus (7/5) 19 2 ∧
    treeBonus (7/5) 19 2 ≤ ((17134229/10000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((14978661/5000000)) ((29957323/10000000)) ((6119367/5000000)) ((2447747/2000000)) 19 2
    (by norm_num) (by norm_num)
    log_20_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_19_3 : ((17487547/12500000):ℝ) ≤ treeBonus (7/5) 19 3 ∧
    treeBonus (7/5) 19 3 ≤ ((13990039/10000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((14978661/5000000)) ((29957323/10000000)) ((2498221/2500000)) ((1998577/2000000)) 19 3
    (by norm_num) (by norm_num)
    log_20_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_19_4 : ((60578637/50000000):ℝ) ≤ treeBonus (7/5) 19 4 ∧
    treeBonus (7/5) 19 4 ≤ ((15144661/12500000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((14978661/5000000)) ((29957323/10000000)) ((8654091/10000000)) ((2163523/2500000)) 19 4
    (by norm_num) (by norm_num)
    log_20_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_19_5 : ((10836637/10000000):ℝ) ≤ treeBonus (7/5) 19 5 ∧
    treeBonus (7/5) 19 5 ≤ ((6772899/6250000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((14978661/5000000)) ((29957323/10000000)) ((1548091/2000000)) ((967557/1250000)) 19 5
    (by norm_num) (by norm_num)
    log_20_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_19_6 : ((12365563/12500000):ℝ) ≤ treeBonus (7/5) 19 6 ∧
    treeBonus (7/5) 19 6 ≤ ((49462259/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((14978661/5000000)) ((29957323/10000000)) ((1766509/2500000)) ((7066037/10000000)) 19 6
    (by norm_num) (by norm_num)
    log_20_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_19_8 : ((42835569/50000000):ℝ) ≤ treeBonus (7/5) 19 8 ∧
    treeBonus (7/5) 19 8 ≤ ((5354447/6250000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((14978661/5000000)) ((29957323/10000000)) ((6119367/10000000)) ((764921/1250000)) 19 8
    (by norm_num) (by norm_num)
    log_20_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_20_2 : ((43182979/25000000):ℝ) ≤ treeBonus (7/5) 20 2 ∧
    treeBonus (7/5) 20 2 ≤ ((21591493/12500000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((3805653/1250000)) ((1217809/400000)) ((6168997/5000000)) ((3084499/2500000)) 20 2
    (by norm_num) (by norm_num)
    log_21_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_20_3 : ((7051751/5000000):ℝ) ≤ treeBonus (7/5) 20 3 ∧
    treeBonus (7/5) 20 3 ≤ ((70517517/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((3805653/1250000)) ((1217809/400000)) ((1007393/1000000)) ((10073931/10000000)) 20 3
    (by norm_num) (by norm_num)
    log_21_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_20_4 : ((61069953/50000000):ℝ) ≤ treeBonus (7/5) 20 4 ∧
    treeBonus (7/5) 20 4 ≤ ((61069967/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((3805653/1250000)) ((1217809/400000)) ((8724279/10000000)) ((8724281/10000000)) 20 4
    (by norm_num) (by norm_num)
    log_21_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_20_5 : ((54622631/50000000):ℝ) ≤ treeBonus (7/5) 20 5 ∧
    treeBonus (7/5) 20 5 ≤ ((27311319/25000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((3805653/1250000)) ((1217809/400000)) ((7803233/10000000)) ((3901617/5000000)) 20 5
    (by norm_num) (by norm_num)
    log_21_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_20_6 : ((3116463/3125000):ℝ) ≤ treeBonus (7/5) 20 6 ∧
    treeBonus (7/5) 20 6 ≤ ((9972683/10000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((3805653/1250000)) ((1217809/400000)) ((445209/625000)) ((1424669/2000000)) 20 6
    (by norm_num) (by norm_num)
    log_21_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_20_7 : ((9232909/10000000):ℝ) ≤ treeBonus (7/5) 20 7 ∧
    treeBonus (7/5) 20 7 ≤ ((5770569/6250000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((3805653/1250000)) ((1217809/400000)) ((1318987/2000000)) ((824367/1250000)) 20 7
    (by norm_num) (by norm_num)
    log_21_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_20_8 : ((43182979/50000000):ℝ) ≤ treeBonus (7/5) 20 8 ∧
    treeBonus (7/5) 20 8 ≤ ((21591493/25000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((3805653/1250000)) ((1217809/400000)) ((6168997/10000000)) ((3084499/5000000)) 20 8
    (by norm_num) (by norm_num)
    log_21_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_21_2 : ((87023293/50000000):ℝ) ≤ treeBonus (7/5) 21 2 ∧
    treeBonus (7/5) 21 2 ≤ ((870233/500000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((3863803/1250000)) ((1236417/400000)) ((12431899/10000000)) ((124319/100000)) 21 2
    (by norm_num) (by norm_num)
    log_22_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_21_3 : ((71054221/50000000):ℝ) ≤ treeBonus (7/5) 21 3 ∧
    treeBonus (7/5) 21 3 ≤ ((17763557/12500000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((3863803/1250000)) ((1236417/400000)) ((10150603/10000000)) ((2537651/2500000)) 21 3
    (by norm_num) (by norm_num)
    log_22_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_21_4 : ((1538369/1250000):ℝ) ≤ treeBonus (7/5) 21 4 ∧
    treeBonus (7/5) 21 4 ≤ ((61534767/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((3863803/1250000)) ((1236417/400000)) ((219767/250000)) ((8790681/10000000)) 21 4
    (by norm_num) (by norm_num)
    log_22_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_21_6 : ((1256073/1250000):ℝ) ≤ treeBonus (7/5) 21 6 ∧
    treeBonus (7/5) 21 6 ≤ ((50242927/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((3863803/1250000)) ((1236417/400000)) ((179439/250000)) ((7177561/10000000)) 21 6
    (by norm_num) (by norm_num)
    log_22_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_21_7 : ((46515903/50000000):ℝ) ≤ treeBonus (7/5) 21 7 ∧
    treeBonus (7/5) 21 7 ≤ ((4651591/5000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((3863803/1250000)) ((1236417/400000)) ((6645129/10000000)) ((664513/1000000)) 21 7
    (by norm_num) (by norm_num)
    log_22_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_21_8 : ((43511643/50000000):ℝ) ≤ treeBonus (7/5) 21 8 ∧
    treeBonus (7/5) 21 8 ≤ ((870233/1000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((3863803/1250000)) ((1236417/400000)) ((6215949/10000000)) ((124319/200000)) 21 8
    (by norm_num) (by norm_num)
    log_22_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_22_2 : ((8764679/5000000):ℝ) ≤ treeBonus (7/5) 22 2 ∧
    treeBonus (7/5) 22 2 ≤ ((21911701/12500000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((15677471/5000000)) ((31354943/10000000)) ((1252097/1000000)) ((3130243/2500000)) 22 2
    (by norm_num) (by norm_num)
    log_23_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_22_3 : ((71563303/50000000):ℝ) ≤ treeBonus (7/5) 22 3 ∧
    treeBonus (7/5) 22 3 ≤ ((71563317/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((15677471/5000000)) ((31354943/10000000)) ((10223329/10000000)) ((10223331/10000000)) 22 3
    (by norm_num) (by norm_num)
    log_23_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_22_4 : ((61975641/50000000):ℝ) ≤ treeBonus (7/5) 22 4 ∧
    treeBonus (7/5) 22 4 ≤ ((1936739/1562500):ℝ) := by
  have h := uct_bonus_interval (7/5) ((15677471/5000000)) ((31354943/10000000)) ((8853663/10000000)) ((276677/312500)) 22 4
    (by norm_num) (by norm_num)
    log_23_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_22_6 : ((10120579/10000000):ℝ) ≤ treeBonus (7/5) 22 6 ∧
    treeBonus (7/5) 22 6 ≤ ((25301451/25000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((15677471/5000000)) ((31354943/10000000)) ((1445797/2000000)) ((3614493/5000000)) 22 6
    (by norm_num) (by norm_num)
    log_23_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_22_7 : ((2342459/2500000):ℝ) ≤ treeBonus (7/5) 22 7 ∧
    treeBonus (7/5) 22 7 ≤ ((46849187/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((15677471/5000000)) ((31354943/10000000)) ((334637/500000)) ((6692741/10000000)) 22 7
    (by norm_num) (by norm_num)
    log_23_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_22_9 : ((20658547/25000000):ℝ) ≤ treeBonus (7/5) 22 9 ∧
    treeBonus (7/5) 22 9 ≤ ((41317101/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((15677471/5000000)) ((31354943/10000000)) ((2951221/5000000)) ((5902443/10000000)) 22 9
    (by norm_num) (by norm_num)
    log_23_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_23_2 : ((88239627/50000000):ℝ) ≤ treeBonus (7/5) 23 2 ∧
    treeBonus (7/5) 23 2 ≤ ((44119817/25000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((15890269/5000000)) ((31780539/10000000)) ((12605661/10000000)) ((6302831/5000000)) 23 2
    (by norm_num) (by norm_num)
    log_24_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_23_3 : ((72047353/50000000):ℝ) ≤ treeBonus (7/5) 23 3 ∧
    treeBonus (7/5) 23 3 ≤ ((112574/78125):ℝ) := by
  have h := uct_bonus_interval (7/5) ((15890269/5000000)) ((31780539/10000000)) ((10292479/10000000)) ((16082/15625)) 23 3
    (by norm_num) (by norm_num)
    log_24_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_23_4 : ((15598709/12500000):ℝ) ≤ treeBonus (7/5) 23 4 ∧
    treeBonus (7/5) 23 4 ≤ ((62394843/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((15890269/5000000)) ((31780539/10000000)) ((2228387/2500000)) ((8913549/10000000)) 23 4
    (by norm_num) (by norm_num)
    log_24_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_23_6 : ((50945167/50000000):ℝ) ≤ treeBonus (7/5) 23 6 ∧
    treeBonus (7/5) 23 6 ≤ ((25472587/25000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((15890269/5000000)) ((31780539/10000000)) ((7277881/10000000)) ((3638941/5000000)) 23 6
    (by norm_num) (by norm_num)
    log_24_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_23_7 : ((47166063/50000000):ℝ) ≤ treeBonus (7/5) 23 7 ∧
    treeBonus (7/5) 23 7 ≤ ((4716607/5000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((15890269/5000000)) ((31780539/10000000)) ((6738009/10000000)) ((673801/1000000)) 23 7
    (by norm_num) (by norm_num)
    log_24_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_23_8 : ((4411981/5000000):ℝ) ≤ treeBonus (7/5) 23 8 ∧
    treeBonus (7/5) 23 8 ≤ ((44119817/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((15890269/5000000)) ((31780539/10000000)) ((630283/1000000)) ((6302831/10000000)) 23 8
    (by norm_num) (by norm_num)
    log_24_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_23_9 : ((8319311/10000000):ℝ) ≤ treeBonus (7/5) 23 9 ∧
    treeBonus (7/5) 23 9 ≤ ((20798281/25000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((15890269/5000000)) ((31780539/10000000)) ((1188473/2000000)) ((2971183/5000000)) 23 9
    (by norm_num) (by norm_num)
    log_24_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_24_2 : ((44402267/25000000):ℝ) ≤ treeBonus (7/5) 24 2 ∧
    treeBonus (7/5) 24 2 ≤ ((88804541/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((16094379/5000000)) ((32188759/10000000)) ((6343181/5000000)) ((12686363/10000000)) 24 2
    (by norm_num) (by norm_num)
    log_25_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_24_3 : ((72508597/50000000):ℝ) ≤ treeBonus (7/5) 24 3 ∧
    treeBonus (7/5) 24 3 ≤ ((18127151/12500000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((16094379/5000000)) ((32188759/10000000)) ((10358371/10000000)) ((2589593/2500000)) 24 3
    (by norm_num) (by norm_num)
    log_25_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_24_4 : ((15698571/12500000):ℝ) ≤ treeBonus (7/5) 24 4 ∧
    treeBonus (7/5) 24 4 ≤ ((62794291/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((16094379/5000000)) ((32188759/10000000)) ((2242653/2500000)) ((8970613/10000000)) 24 4
    (by norm_num) (by norm_num)
    log_25_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_24_7 : ((9493603/10000000):ℝ) ≤ treeBonus (7/5) 24 7 ∧
    treeBonus (7/5) 24 7 ≤ ((47468029/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((16094379/5000000)) ((32188759/10000000)) ((1356229/2000000)) ((6781147/10000000)) 24 7
    (by norm_num) (by norm_num)
    log_25_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_24_8 : ((44402267/50000000):ℝ) ≤ treeBonus (7/5) 24 8 ∧
    treeBonus (7/5) 24 8 ≤ ((22201137/25000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((16094379/5000000)) ((32188759/10000000)) ((6343181/10000000)) ((3171591/5000000)) 24 8
    (by norm_num) (by norm_num)
    log_25_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_24_9 : ((5232857/6250000):ℝ) ≤ treeBonus (7/5) 24 9 ∧
    treeBonus (7/5) 24 9 ≤ ((41862863/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((16094379/5000000)) ((32188759/10000000)) ((747551/1250000)) ((5980409/10000000)) 24 9
    (by norm_num) (by norm_num)
    log_25_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_25_2 : ((89343919/50000000):ℝ) ≤ treeBonus (7/5) 25 2 ∧
    treeBonus (7/5) 25 2 ≤ ((44671963/25000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((6516193/2000000)) ((16290483/5000000)) ((12763417/10000000)) ((6381709/5000000)) 25 2
    (by norm_num) (by norm_num)
    log_26_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_25_3 : ((36474501/25000000):ℝ) ≤ treeBonus (7/5) 25 3 ∧
    treeBonus (7/5) 25 3 ≤ ((72949009/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((6516193/2000000)) ((16290483/5000000)) ((5210643/5000000)) ((10421287/10000000)) 25 3
    (by norm_num) (by norm_num)
    log_26_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_25_4 : ((63175693/50000000):ℝ) ≤ treeBonus (7/5) 25 4 ∧
    treeBonus (7/5) 25 4 ≤ ((631757/500000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((6516193/2000000)) ((16290483/5000000)) ((9025099/10000000)) ((90251/100000)) 25 4
    (by norm_num) (by norm_num)
    log_26_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_25_7 : ((47756331/50000000):ℝ) ≤ treeBonus (7/5) 25 7 ∧
    treeBonus (7/5) 25 7 ≤ ((23878169/25000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((6516193/2000000)) ((16290483/5000000)) ((6822333/10000000)) ((3411167/5000000)) 25 7
    (by norm_num) (by norm_num)
    log_26_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_25_8 : ((11167989/12500000):ℝ) ≤ treeBonus (7/5) 25 8 ∧
    treeBonus (7/5) 25 8 ≤ ((44671963/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((6516193/2000000)) ((16290483/5000000)) ((1595427/2500000)) ((6381709/10000000)) 25 8
    (by norm_num) (by norm_num)
    log_26_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_25_10 : ((39955811/50000000):ℝ) ≤ treeBonus (7/5) 25 10 ∧
    treeBonus (7/5) 25 10 ≤ ((19977909/25000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((6516193/2000000)) ((16290483/5000000)) ((5707973/10000000)) ((2853987/5000000)) 25 10
    (by norm_num) (by norm_num)
    log_26_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_26_3 : ((7337029/5000000):ℝ) ≤ treeBonus (7/5) 26 3 ∧
    treeBonus (7/5) 26 3 ≤ ((73370297/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((1029949/312500)) ((32958369/10000000)) ((1048147/1000000)) ((10481471/10000000)) 26 3
    (by norm_num) (by norm_num)
    log_27_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_26_4 : ((63540533/50000000):ℝ) ≤ treeBonus (7/5) 26 4 ∧
    treeBonus (7/5) 26 4 ≤ ((3177027/2500000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((1029949/312500)) ((32958369/10000000)) ((9077219/10000000)) ((453861/500000)) 26 4
    (by norm_num) (by norm_num)
    log_27_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_26_7 : ((48032131/50000000):ℝ) ≤ treeBonus (7/5) 26 7 ∧
    treeBonus (7/5) 26 7 ≤ ((24016069/25000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((1029949/312500)) ((32958369/10000000)) ((6861733/10000000)) ((3430867/5000000)) 26 7
    (by norm_num) (by norm_num)
    log_27_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_26_8 : ((44929941/50000000):ℝ) ≤ treeBonus (7/5) 26 8 ∧
    treeBonus (7/5) 26 8 ≤ ((11232487/12500000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((1029949/312500)) ((32958369/10000000)) ((6418563/10000000)) ((1604641/2500000)) 26 8
    (by norm_num) (by norm_num)
    log_27_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_26_9 : ((42360353/50000000):ℝ) ≤ treeBonus (7/5) 26 9 ∧
    treeBonus (7/5) 26 9 ≤ ((1059009/1250000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((1029949/312500)) ((32958369/10000000)) ((6051479/10000000)) ((151287/250000)) 26 9
    (by norm_num) (by norm_num)
    log_27_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_26_10 : ((40186559/50000000):ℝ) ≤ treeBonus (7/5) 26 10 ∧
    treeBonus (7/5) 26 10 ≤ ((20093283/25000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((1029949/312500)) ((32958369/10000000)) ((5740937/10000000)) ((2870469/5000000)) 26 10
    (by norm_num) (by norm_num)
    log_27_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_27_3 : ((3688699/2500000):ℝ) ≤ treeBonus (7/5) 27 3 ∧
    treeBonus (7/5) 27 3 ≤ ((73773987/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((6664409/2000000)) ((16661023/5000000)) ((526957/500000)) ((10539141/10000000)) 27 3
    (by norm_num) (by norm_num)
    log_28_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_27_4 : ((63890141/50000000):ℝ) ≤ treeBonus (7/5) 27 4 ∧
    treeBonus (7/5) 27 4 ≤ ((15972537/12500000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((6664409/2000000)) ((16661023/5000000)) ((9127163/10000000)) ((2281791/2500000)) 27 4
    (by norm_num) (by norm_num)
    log_28_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_27_5 : ((57145081/50000000):ℝ) ≤ treeBonus (7/5) 27 5 ∧
    treeBonus (7/5) 27 5 ≤ ((446446/390625):ℝ) := by
  have h := uct_bonus_interval (7/5) ((6664409/2000000)) ((16661023/5000000)) ((8163583/10000000)) ((63778/78125)) 27 5
    (by norm_num) (by norm_num)
    log_28_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_27_8 : ((45177153/50000000):ℝ) ≤ treeBonus (7/5) 27 8 ∧
    treeBonus (7/5) 27 8 ≤ ((1129429/1250000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((6664409/2000000)) ((16661023/5000000)) ((6453879/10000000)) ((161347/250000)) 27 8
    (by norm_num) (by norm_num)
    log_28_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_27_9 : ((1703737/2000000):ℝ) ≤ treeBonus (7/5) 27 9 ∧
    treeBonus (7/5) 27 9 ≤ ((5324179/6250000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((6664409/2000000)) ((16661023/5000000)) ((243391/400000)) ((760597/1250000)) 27 9
    (by norm_num) (by norm_num)
    log_28_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_27_10 : ((1616307/2000000):ℝ) ≤ treeBonus (7/5) 27 10 ∧
    treeBonus (7/5) 27 10 ≤ ((20203841/25000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((6664409/2000000)) ((16661023/5000000)) ((230901/400000)) ((2886263/5000000)) 27 10
    (by norm_num) (by norm_num)
    log_28_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_28_3 : ((9270177/6250000):ℝ) ≤ treeBonus (7/5) 28 3 ∧
    treeBonus (7/5) 28 3 ≤ ((74161423/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((16836479/5000000)) ((33672959/10000000)) ((1324311/1250000)) ((10594489/10000000)) 28 3
    (by norm_num) (by norm_num)
    log_29_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_28_4 : ((8028209/6250000):ℝ) ≤ treeBonus (7/5) 28 4 ∧
    treeBonus (7/5) 28 4 ≤ ((64225679/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((16836479/5000000)) ((33672959/10000000)) ((1146887/1250000)) ((9175097/10000000)) 28 4
    (by norm_num) (by norm_num)
    log_29_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_28_5 : ((11489037/10000000):ℝ) ≤ treeBonus (7/5) 28 5 ∧
    treeBonus (7/5) 28 5 ≤ ((7180649/6250000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((16836479/5000000)) ((33672959/10000000)) ((1641291/2000000)) ((1025807/1250000)) 28 5
    (by norm_num) (by norm_num)
    log_29_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_28_6 : ((26220019/25000000):ℝ) ≤ treeBonus (7/5) 28 6 ∧
    treeBonus (7/5) 28 6 ≤ ((10488009/10000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((16836479/5000000)) ((33672959/10000000)) ((3745717/5000000)) ((1498287/2000000)) 28 6
    (by norm_num) (by norm_num)
    log_29_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_28_8 : ((11353601/12500000):ℝ) ≤ treeBonus (7/5) 28 8 ∧
    treeBonus (7/5) 28 8 ≤ ((22707209/25000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((16836479/5000000)) ((33672959/10000000)) ((1621943/2500000)) ((3243887/5000000)) 28 8
    (by norm_num) (by norm_num)
    log_29_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_28_9 : ((4281711/5000000):ℝ) ≤ treeBonus (7/5) 28 9 ∧
    treeBonus (7/5) 28 9 ≤ ((10704281/12500000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((16836479/5000000)) ((33672959/10000000)) ((611673/1000000)) ((1529183/2500000)) 28 9
    (by norm_num) (by norm_num)
    log_29_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_28_11 : ((38729537/50000000):ℝ) ≤ treeBonus (7/5) 28 11 ∧
    treeBonus (7/5) 28 11 ≤ ((4841193/6250000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((16836479/5000000)) ((33672959/10000000)) ((5532791/10000000)) ((691599/1250000)) 28 11
    (by norm_num) (by norm_num)
    log_29_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_29_3 : ((74533809/50000000):ℝ) ≤ treeBonus (7/5) 29 3 ∧
    treeBonus (7/5) 29 3 ≤ ((9316727/6250000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((34011973/10000000)) ((17005987/5000000)) ((10647687/10000000)) ((1330961/1250000)) 29 3
    (by norm_num) (by norm_num)
    log_30_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_29_4 : ((64548169/50000000):ℝ) ≤ treeBonus (7/5) 29 4 ∧
    treeBonus (7/5) 29 4 ≤ ((4034261/3125000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((34011973/10000000)) ((17005987/5000000)) ((9221167/10000000)) ((576323/625000)) 29 4
    (by norm_num) (by norm_num)
    log_30_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_29_5 : ((57733641/50000000):ℝ) ≤ treeBonus (7/5) 29 5 ∧
    treeBonus (7/5) 29 5 ≤ ((3608353/3125000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((34011973/10000000)) ((17005987/5000000)) ((8247663/10000000)) ((515479/625000)) 29 5
    (by norm_num) (by norm_num)
    log_30_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_29_6 : ((52703357/50000000):ℝ) ≤ treeBonus (7/5) 29 6 ∧
    treeBonus (7/5) 29 6 ≤ ((13175841/12500000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((34011973/10000000)) ((17005987/5000000)) ((7529051/10000000)) ((1882263/2500000)) 29 6
    (by norm_num) (by norm_num)
    log_30_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_29_8 : ((912849/1000000):ℝ) ≤ treeBonus (7/5) 29 8 ∧
    treeBonus (7/5) 29 8 ≤ ((45642457/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((34011973/10000000)) ((17005987/5000000)) ((130407/200000)) ((6520351/10000000)) 29 8
    (by norm_num) (by norm_num)
    log_30_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_29_9 : ((8606423/10000000):ℝ) ≤ treeBonus (7/5) 29 9 ∧
    treeBonus (7/5) 29 9 ≤ ((21516061/25000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((34011973/10000000)) ((17005987/5000000)) ((1229489/2000000)) ((3073723/5000000)) 29 9
    (by norm_num) (by norm_num)
    log_30_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_29_10 : ((20411923/25000000):ℝ) ≤ treeBonus (7/5) 29 10 ∧
    treeBonus (7/5) 29 10 ≤ ((40823853/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((34011973/10000000)) ((17005987/5000000)) ((2915989/5000000)) ((5831979/10000000)) 29 10
    (by norm_num) (by norm_num)
    log_30_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_29_12 : ((37266901/50000000):ℝ) ≤ treeBonus (7/5) 29 12 ∧
    treeBonus (7/5) 29 12 ≤ ((9316727/12500000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((34011973/10000000)) ((17005987/5000000)) ((5323843/10000000)) ((1330961/2500000)) 29 12
    (by norm_num) (by norm_num)
    log_30_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_30_3 : ((74892223/50000000):ℝ) ≤ treeBonus (7/5) 30 3 ∧
    treeBonus (7/5) 30 3 ≤ ((7489223/5000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((1073121/312500)) ((34339873/10000000)) ((10698889/10000000)) ((1069889/1000000)) 30 3
    (by norm_num) (by norm_num)
    log_31_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_30_4 : ((6485857/5000000):ℝ) ≤ treeBonus (7/5) 30 4 ∧
    treeBonus (7/5) 30 4 ≤ ((64858577/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((1073121/312500)) ((34339873/10000000)) ((926551/1000000)) ((9265511/10000000)) 30 4
    (by norm_num) (by norm_num)
    log_31_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_30_5 : ((14502817/12500000):ℝ) ≤ treeBonus (7/5) 30 5 ∧
    treeBonus (7/5) 30 5 ≤ ((2320451/2000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((1073121/312500)) ((34339873/10000000)) ((2071831/2500000)) ((331493/400000)) 30 5
    (by norm_num) (by norm_num)
    log_31_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_30_7 : ((49028469/50000000):ℝ) ≤ treeBonus (7/5) 30 7 ∧
    treeBonus (7/5) 30 7 ≤ ((12257119/12500000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((1073121/312500)) ((34339873/10000000)) ((7004067/10000000)) ((1751017/2500000)) 30 7
    (by norm_num) (by norm_num)
    log_31_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_30_8 : ((9172387/10000000):ℝ) ≤ treeBonus (7/5) 30 8 ∧
    treeBonus (7/5) 30 8 ≤ ((22930971/25000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((1073121/312500)) ((34339873/10000000)) ((1310341/2000000)) ((3275853/5000000)) 30 8
    (by norm_num) (by norm_num)
    log_31_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_30_9 : ((21619521/25000000):ℝ) ≤ treeBonus (7/5) 30 9 ∧
    treeBonus (7/5) 30 9 ≤ ((43239049/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((1073121/312500)) ((34339873/10000000)) ((3088503/5000000)) ((6177007/10000000)) 30 9
    (by norm_num) (by norm_num)
    log_31_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_30_10 : ((41020161/50000000):ℝ) ≤ treeBonus (7/5) 30 10 ∧
    treeBonus (7/5) 30 10 ≤ ((5127521/6250000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((1073121/312500)) ((34339873/10000000)) ((5860023/10000000)) ((732503/1250000)) 30 10
    (by norm_num) (by norm_num)
    log_31_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_30_12 : ((9361527/12500000):ℝ) ≤ treeBonus (7/5) 30 12 ∧
    treeBonus (7/5) 30 12 ≤ ((7489223/10000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((1073121/312500)) ((34339873/10000000)) ((1337361/2500000)) ((1069889/2000000)) 30 12
    (by norm_num) (by norm_num)
    log_31_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_31_3 : ((75237631/50000000):ℝ) ≤ treeBonus (7/5) 31 3 ∧
    treeBonus (7/5) 31 3 ≤ ((37618819/25000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((34657359/10000000)) ((433217/125000)) ((10748233/10000000)) ((5374117/5000000)) 31 3
    (by norm_num) (by norm_num)
    log_32_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_31_4 : ((65157701/50000000):ℝ) ≤ treeBonus (7/5) 31 4 ∧
    treeBonus (7/5) 31 4 ≤ ((16289427/12500000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((34657359/10000000)) ((433217/125000)) ((9308243/10000000)) ((2327061/2500000)) 31 4
    (by norm_num) (by norm_num)
    log_32_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_31_5 : ((29139411/25000000):ℝ) ≤ treeBonus (7/5) 31 5 ∧
    treeBonus (7/5) 31 5 ≤ ((58278829/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((34657359/10000000)) ((433217/125000)) ((4162773/5000000)) ((8325547/10000000)) 31 5
    (by norm_num) (by norm_num)
    log_32_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_31_7 : ((4925459/5000000):ℝ) ≤ treeBonus (7/5) 31 7 ∧
    treeBonus (7/5) 31 7 ≤ ((49254597/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((34657359/10000000)) ((433217/125000)) ((703637/1000000)) ((7036371/10000000)) 31 7
    (by norm_num) (by norm_num)
    log_32_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_31_9 : ((8687693/10000000):ℝ) ≤ treeBonus (7/5) 31 9 ∧
    treeBonus (7/5) 31 9 ≤ ((5429809/6250000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((34657359/10000000)) ((433217/125000)) ((1241099/2000000)) ((775687/1250000)) 31 9
    (by norm_num) (by norm_num)
    log_32_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_31_10 : ((824187/1000000):ℝ) ≤ treeBonus (7/5) 31 10 ∧
    treeBonus (7/5) 31 10 ≤ ((41209357/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((34657359/10000000)) ((433217/125000)) ((117741/200000)) ((5887051/10000000)) 31 10
    (by norm_num) (by norm_num)
    log_32_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_31_12 : ((9404703/12500000):ℝ) ≤ treeBonus (7/5) 31 12 ∧
    treeBonus (7/5) 31 12 ≤ ((37618819/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((34657359/10000000)) ((433217/125000)) ((1343529/2500000)) ((5374117/10000000)) 31 12
    (by norm_num) (by norm_num)
    log_32_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_32_3 : ((75570901/50000000):ℝ) ≤ treeBonus (7/5) 32 3 ∧
    treeBonus (7/5) 32 3 ≤ ((37785461/25000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((34965071/10000000)) ((34965081/10000000)) ((10795843/10000000)) ((5397923/5000000)) 32 3
    (by norm_num) (by norm_num)
    log_33_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_32_4 : ((32723159/25000000):ℝ) ≤ treeBonus (7/5) 32 4 ∧
    treeBonus (7/5) 32 4 ≤ ((65446339/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((34965071/10000000)) ((34965081/10000000)) ((4674737/5000000)) ((9349477/10000000)) 32 4
    (by norm_num) (by norm_num)
    log_33_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_32_5 : ((7317121/6250000):ℝ) ≤ treeBonus (7/5) 32 5 ∧
    treeBonus (7/5) 32 5 ≤ ((29268491/25000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((34965071/10000000)) ((34965081/10000000)) ((1045303/1250000)) ((4181213/5000000)) 32 5
    (by norm_num) (by norm_num)
    log_33_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_32_7 : ((24736383/25000000):ℝ) ≤ treeBonus (7/5) 32 7 ∧
    treeBonus (7/5) 32 7 ≤ ((2473639/2500000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((34965071/10000000)) ((34965081/10000000)) ((3533769/5000000)) ((353377/500000)) 32 7
    (by norm_num) (by norm_num)
    log_33_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_32_9 : ((43630881/50000000):ℝ) ≤ treeBonus (7/5) 32 9 ∧
    treeBonus (7/5) 32 9 ≤ ((8726179/10000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((34965071/10000000)) ((34965081/10000000)) ((6232983/10000000)) ((1246597/2000000)) 32 9
    (by norm_num) (by norm_num)
    log_33_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_32_10 : ((41391889/50000000):ℝ) ≤ treeBonus (7/5) 32 10 ∧
    treeBonus (7/5) 32 10 ≤ ((5173987/6250000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((34965071/10000000)) ((34965081/10000000)) ((5913127/10000000)) ((739141/1250000)) 32 10
    (by norm_num) (by norm_num)
    log_33_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_32_11 : ((7893123/10000000):ℝ) ≤ treeBonus (7/5) 32 11 ∧
    treeBonus (7/5) 32 11 ≤ ((39465629/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((34965071/10000000)) ((34965081/10000000)) ((1127589/2000000)) ((5637947/10000000)) 32 11
    (by norm_num) (by norm_num)
    log_33_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_32_13 : ((7260617/10000000):ℝ) ≤ treeBonus (7/5) 32 13 ∧
    treeBonus (7/5) 32 13 ≤ ((36303099/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((34965071/10000000)) ((34965081/10000000)) ((1037231/2000000)) ((5186157/10000000)) 32 13
    (by norm_num) (by norm_num)
    log_33_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_33_3 : ((75892831/50000000):ℝ) ≤ treeBonus (7/5) 33 3 ∧
    treeBonus (7/5) 33 3 ≤ ((37946419/25000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((35263603/10000000)) ((4407951/1250000)) ((10841833/10000000)) ((5420917/5000000)) 33 3
    (by norm_num) (by norm_num)
    log_34_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_33_4 : ((32862557/25000000):ℝ) ≤ treeBonus (7/5) 33 4 ∧
    treeBonus (7/5) 33 4 ≤ ((8215641/6250000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((35263603/10000000)) ((4407951/1250000)) ((4694651/5000000)) ((1173663/1250000)) 33 4
    (by norm_num) (by norm_num)
    log_34_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_33_5 : ((58786329/50000000):ℝ) ≤ treeBonus (7/5) 33 5 ∧
    treeBonus (7/5) 33 5 ≤ ((58786343/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((35263603/10000000)) ((4407951/1250000)) ((8398047/10000000)) ((8398049/10000000)) 33 5
    (by norm_num) (by norm_num)
    log_34_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_33_7 : ((9936703/10000000):ℝ) ≤ treeBonus (7/5) 33 7 ∧
    treeBonus (7/5) 33 7 ≤ ((49683529/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((35263603/10000000)) ((4407951/1250000)) ((1419529/2000000)) ((7097647/10000000)) 33 7
    (by norm_num) (by norm_num)
    log_34_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_33_9 : ((8763349/10000000):ℝ) ≤ treeBonus (7/5) 33 9 ∧
    treeBonus (7/5) 33 9 ≤ ((2738547/3125000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((35263603/10000000)) ((4407951/1250000)) ((1251907/2000000)) ((391221/625000)) 33 9
    (by norm_num) (by norm_num)
    log_34_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_33_10 : ((10392053/12500000):ℝ) ≤ treeBonus (7/5) 33 10 ∧
    treeBonus (7/5) 33 10 ≤ ((41568219/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((35263603/10000000)) ((4407951/1250000)) ((1484579/2500000)) ((5938317/10000000)) 33 10
    (by norm_num) (by norm_num)
    log_34_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_33_11 : ((19816867/25000000):ℝ) ≤ treeBonus (7/5) 33 11 ∧
    treeBonus (7/5) 33 11 ≤ ((9908437/12500000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((35263603/10000000)) ((4407951/1250000)) ((2830981/5000000)) ((1415491/2500000)) 33 11
    (by norm_num) (by norm_num)
    log_34_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_33_13 : ((4557217/6250000):ℝ) ≤ treeBonus (7/5) 33 13 ∧
    treeBonus (7/5) 33 13 ≤ ((36457743/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((35263603/10000000)) ((4407951/1250000)) ((651031/1250000)) ((5208249/10000000)) 33 13
    (by norm_num) (by norm_num)
    log_34_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_34_3 : ((76204121/50000000):ℝ) ≤ treeBonus (7/5) 34 3 ∧
    treeBonus (7/5) 34 3 ≤ ((2381379/1562500):ℝ) := by
  have h := uct_bonus_interval (7/5) ((35553479/10000000)) ((17776741/5000000)) ((10886303/10000000)) ((340197/312500)) 34 3
    (by norm_num) (by norm_num)
    log_35_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_34_4 : ((13198941/10000000):ℝ) ≤ treeBonus (7/5) 34 4 ∧
    treeBonus (7/5) 34 4 ≤ ((8249339/6250000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((35553479/10000000)) ((17776741/5000000)) ((1885563/2000000)) ((1178477/1250000)) 34 4
    (by norm_num) (by norm_num)
    log_35_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_34_5 : ((29513729/25000000):ℝ) ≤ treeBonus (7/5) 34 5 ∧
    treeBonus (7/5) 34 5 ≤ ((11805493/10000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((35553479/10000000)) ((17776741/5000000)) ((4216247/5000000)) ((1686499/2000000)) 34 5
    (by norm_num) (by norm_num)
    log_35_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_34_7 : ((24943653/25000000):ℝ) ≤ treeBonus (7/5) 34 7 ∧
    treeBonus (7/5) 34 7 ≤ ((49887313/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((35553479/10000000)) ((17776741/5000000)) ((3563379/5000000)) ((7126759/10000000)) 34 7
    (by norm_num) (by norm_num)
    log_35_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_34_10 : ((41738711/50000000):ℝ) ≤ treeBonus (7/5) 34 10 ∧
    treeBonus (7/5) 34 10 ≤ ((1669549/2000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((35553479/10000000)) ((17776741/5000000)) ((5962673/10000000)) ((238507/400000)) 34 10
    (by norm_num) (by norm_num)
    log_35_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_34_11 : ((19898151/25000000):ℝ) ≤ treeBonus (7/5) 34 11 ∧
    treeBonus (7/5) 34 11 ≤ ((39796309/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((35553479/10000000)) ((17776741/5000000)) ((2842593/5000000)) ((5685187/10000000)) 34 11
    (by norm_num) (by norm_num)
    log_35_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_34_13 : ((3660727/5000000):ℝ) ≤ treeBonus (7/5) 34 13 ∧
    treeBonus (7/5) 34 13 ≤ ((9151821/12500000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((35553479/10000000)) ((17776741/5000000)) ((522961/1000000)) ((1307403/2500000)) 34 13
    (by norm_num) (by norm_num)
    log_35_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_35_3 : ((76505429/50000000):ℝ) ≤ treeBonus (7/5) 35 3 ∧
    treeBonus (7/5) 35 3 ≤ ((19126359/12500000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((8958797/2500000)) ((3583519/1000000)) ((10929347/10000000)) ((2732337/2500000)) 35 3
    (by norm_num) (by norm_num)
    log_36_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_35_4 : ((16563911/12500000):ℝ) ≤ treeBonus (7/5) 35 4 ∧
    treeBonus (7/5) 35 4 ≤ ((66255651/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((8958797/2500000)) ((3583519/1000000)) ((2366273/2500000)) ((9465093/10000000)) 35 4
    (by norm_num) (by norm_num)
    log_36_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_35_5 : ((11852169/10000000):ℝ) ≤ treeBonus (7/5) 35 5 ∧
    treeBonus (7/5) 35 5 ≤ ((59260859/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((8958797/2500000)) ((3583519/1000000)) ((1693167/2000000)) ((8465837/10000000)) 35 5
    (by norm_num) (by norm_num)
    log_36_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_35_6 : ((10819501/10000000):ℝ) ≤ treeBonus (7/5) 35 6 ∧
    treeBonus (7/5) 35 6 ≤ ((6762189/6250000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((8958797/2500000)) ((3583519/1000000)) ((1545643/2000000)) ((966027/1250000)) 35 6
    (by norm_num) (by norm_num)
    log_36_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_35_7 : ((50084559/50000000):ℝ) ≤ treeBonus (7/5) 35 7 ∧
    treeBonus (7/5) 35 7 ≤ ((25042283/25000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((8958797/2500000)) ((3583519/1000000)) ((7154937/10000000)) ((3577469/5000000)) 35 7
    (by norm_num) (by norm_num)
    log_36_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_35_10 : ((41903743/50000000):ℝ) ≤ treeBonus (7/5) 35 10 ∧
    treeBonus (7/5) 35 10 ≤ ((41903757/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((8958797/2500000)) ((3583519/1000000)) ((5986249/10000000)) ((5986251/10000000)) 35 10
    (by norm_num) (by norm_num)
    log_36_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_35_11 : ((7990731/10000000):ℝ) ≤ treeBonus (7/5) 35 11 ∧
    treeBonus (7/5) 35 11 ≤ ((19976831/25000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((8958797/2500000)) ((3583519/1000000)) ((1141533/2000000)) ((2853833/5000000)) 35 11
    (by norm_num) (by norm_num)
    log_36_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_35_12 : ((38252711/50000000):ℝ) ≤ treeBonus (7/5) 35 12 ∧
    treeBonus (7/5) 35 12 ≤ ((19126359/25000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((8958797/2500000)) ((3583519/1000000)) ((5464673/10000000)) ((2732337/5000000)) 35 12
    (by norm_num) (by norm_num)
    log_36_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_35_14 : ((4426891/6250000):ℝ) ≤ treeBonus (7/5) 35 14 ∧
    treeBonus (7/5) 35 14 ≤ ((7083027/10000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((8958797/2500000)) ((3583519/1000000)) ((632413/1250000)) ((1011861/2000000)) 35 14
    (by norm_num) (by norm_num)
    log_36_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_36_4 : ((66508449/50000000):ℝ) ≤ treeBonus (7/5) 36 4 ∧
    treeBonus (7/5) 36 4 ≤ ((8313557/6250000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((18054589/5000000)) ((1805459/500000)) ((9501207/10000000)) ((1187651/1250000)) 36 4
    (by norm_num) (by norm_num)
    log_37_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_36_5 : ((29743483/25000000):ℝ) ≤ treeBonus (7/5) 36 5 ∧
    treeBonus (7/5) 36 5 ≤ ((59486973/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((18054589/5000000)) ((1805459/500000)) ((4249069/5000000)) ((8498139/10000000)) 36 5
    (by norm_num) (by norm_num)
    log_37_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_36_7 : ((50275659/50000000):ℝ) ≤ treeBonus (7/5) 36 7 ∧
    treeBonus (7/5) 36 7 ≤ ((50275673/50000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((18054589/5000000)) ((1805459/500000)) ((7182237/10000000)) ((7182239/10000000)) 36 7
    (by norm_num) (by norm_num)
    log_37_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_36_10 : ((42063637/50000000):ℝ) ≤ treeBonus (7/5) 36 10 ∧
    treeBonus (7/5) 36 10 ≤ ((10515911/12500000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((18054589/5000000)) ((1805459/500000)) ((6009091/10000000)) ((1502273/2500000)) 36 10
    (by norm_num) (by norm_num)
    log_37_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_36_11 : ((40106101/50000000):ℝ) ≤ treeBonus (7/5) 36 11 ∧
    treeBonus (7/5) 36 11 ≤ ((10026527/12500000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((18054589/5000000)) ((1805459/500000)) ((5729443/10000000)) ((1432361/2500000)) 36 11
    (by norm_num) (by norm_num)
    log_37_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_36_12 : ((9599667/12500000):ℝ) ≤ treeBonus (7/5) 36 12 ∧
    treeBonus (7/5) 36 12 ≤ ((1535947/2000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((18054589/5000000)) ((1805459/500000)) ((1371381/2500000)) ((219421/400000)) 36 12
    (by norm_num) (by norm_num)
    log_37_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_36_14 : ((35550263/50000000):ℝ) ≤ treeBonus (7/5) 36 14 ∧
    treeBonus (7/5) 36 14 ≤ ((3555027/5000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((18054589/5000000)) ((1805459/500000)) ((5078609/10000000)) ((507861/1000000)) 36 14
    (by norm_num) (by norm_num)
    log_37_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
theorem trajectory_bonus_37_12 : ((2408763/3125000):ℝ) ≤ treeBonus (7/5) 37 12 ∧
    treeBonus (7/5) 37 12 ≤ ((7708043/10000000):ℝ) := by
  have h := uct_bonus_interval (7/5) ((36375861/10000000)) ((18187931/5000000)) ((344109/625000)) ((1101149/2000000)) 37 12
    (by norm_num) (by norm_num)
    log_38_interval (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [treeBonus] at h ⊢
  exact h
end AgentUCT32MConcrete
