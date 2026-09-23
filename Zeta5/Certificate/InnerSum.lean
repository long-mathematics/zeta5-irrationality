import Zeta5.Certificate.InnerPartition

/-! Exact rational integration of the branch data. Each prefix sum is proved
separately so checking does not duplicate a large expanded sum. -/

namespace Zeta5.Certificate

noncomputable def innerPieceValue (i : ℕ) : ℝ :=
  innerSlope i * (1 / innerEndpoint i - 1 / innerEndpoint (i + 1)) +
    innerIntercept i / 2 * (1 / innerEndpoint i ^ 2 - 1 / innerEndpoint (i + 1) ^ 2)

private theorem inner_partial_sum_0 :
    (∑ i ∈ Finset.range 0, innerPieceValue i) = 0 := by simp

private theorem inner_partial_sum_1 :
    (∑ i ∈ Finset.range 1, innerPieceValue i) = (113 / 14700) := by
  rw [Finset.sum_range_succ, inner_partial_sum_0]
  change 0 + ((18 / 5) * (1 / 3 - 1 / (70 / 23)) +
    -6 / 2 * (1 / 3 ^ 2 - 1 / (70 / 23) ^ 2)) = (113 / 14700)
  norm_num

private theorem inner_partial_sum_2 :
    (∑ i ∈ Finset.range 2, innerPieceValue i) = (3319 / 80640) := by
  rw [Finset.sum_range_succ, inner_partial_sum_1]
  change (113 / 14700) + ((49 / 20) * (1 / (70 / 23) - 1 / (120 / 37)) +
    (-5 / 2) / 2 * (1 / (70 / 23) ^ 2 - 1 / (120 / 37) ^ 2)) = (3319 / 80640)
  norm_num

private theorem inner_partial_sum_3 :
    (∑ i ∈ Finset.range 3, innerPieceValue i) = (967 / 22400) := by
  rw [Finset.sum_range_succ, inner_partial_sum_2]
  change (3319 / 80640) + ((283 / 40) * (1 / (120 / 37) - 1 / (140 / 43)) +
    (-35 / 2) / 2 * (1 / (120 / 37) ^ 2 - 1 / (140 / 43) ^ 2)) = (967 / 22400)
  norm_num

private theorem inner_partial_sum_4 :
    (∑ i ∈ Finset.range 4, innerPieceValue i) = (1249 / 22400) := by
  rw [Finset.sum_range_succ, inner_partial_sum_3]
  change (967 / 22400) + ((283 / 40) * (1 / (140 / 43) - 1 / (10 / 3)) +
    (-35 / 2) / 2 * (1 / (140 / 43) ^ 2 - 1 / (10 / 3) ^ 2)) = (1249 / 22400)
  norm_num

private theorem inner_partial_sum_5 :
    (∑ i ∈ Finset.range 5, innerPieceValue i) = (7159 / 89600) := by
  rw [Finset.sum_range_succ, inner_partial_sum_4]
  change (1249 / 22400) + ((277 / 40) * (1 / (10 / 3) - 1 / (80 / 23)) +
    -17 / 2 * (1 / (10 / 3) ^ 2 - 1 / (80 / 23) ^ 2)) = (7159 / 89600)
  norm_num

private theorem inner_partial_sum_6 :
    (∑ i ∈ Finset.range 6, innerPieceValue i) = (6551 / 78400) := by
  rw [Finset.sum_range_succ, inner_partial_sum_5]
  change (7159 / 89600) + ((231 / 40) * (1 / (80 / 23) - 1 / (7 / 2)) +
    -13 / 2 * (1 / (80 / 23) ^ 2 - 1 / (7 / 2) ^ 2)) = (6551 / 78400)
  norm_num

private theorem inner_partial_sum_7 :
    (∑ i ∈ Finset.range 7, innerPieceValue i) = (17331 / 143360) := by
  rw [Finset.sum_range_succ, inner_partial_sum_6]
  change (6551 / 78400) + ((271 / 40) * (1 / (7 / 2) - 1 / (160 / 43)) +
    (-33 / 2) / 2 * (1 / (7 / 2) ^ 2 - 1 / (160 / 43) ^ 2)) = (17331 / 143360)
  norm_num

private theorem inner_partial_sum_8 :
    (∑ i ∈ Finset.range 8, innerPieceValue i) = (16481 / 125440) := by
  rw [Finset.sum_range_succ, inner_partial_sum_7]
  change (17331 / 143360) + ((71 / 20) * (1 / (160 / 43) - 1 / (140 / 37)) +
    (-9 / 2) / 2 * (1 / (160 / 43) ^ 2 - 1 / (140 / 37) ^ 2)) = (16481 / 125440)
  norm_num

private theorem inner_partial_sum_9 :
    (∑ i ∈ Finset.range 9, innerPieceValue i) = (1106299 / 7257600) := by
  rw [Finset.sum_range_succ, inner_partial_sum_8]
  change (16481 / 125440) + ((27 / 5) * (1 / (140 / 37) - 1 / (90 / 23)) +
    (-23 / 2) / 2 * (1 / (140 / 37) ^ 2 - 1 / (90 / 23) ^ 2)) = (1106299 / 7257600)
  norm_num

private theorem inner_partial_sum_10 :
    (∑ i ∈ Finset.range 10, innerPieceValue i) = (26807 / 161280) := by
  rw [Finset.sum_range_succ, inner_partial_sum_9]
  change (1106299 / 7257600) + ((17 / 4) * (1 / (90 / 23) - 1 / 4) +
    -7 / 2 * (1 / (90 / 23) ^ 2 - 1 / 4 ^ 2)) = (26807 / 161280)
  norm_num

private theorem inner_partial_sum_11 :
    (∑ i ∈ Finset.range 11, innerPieceValue i) = (1263659 / 7257600) := by
  rw [Finset.sum_range_succ, inner_partial_sum_10]
  change (26807 / 161280) + ((17 / 5) * (1 / 4 - 1 / (180 / 43)) +
    -11 / 2 * (1 / 4 ^ 2 - 1 / (180 / 43) ^ 2)) = (1263659 / 7257600)
  norm_num

private theorem inner_partial_sum_12 :
    (∑ i ∈ Finset.range 12, innerPieceValue i) = (581689 / 3225600) := by
  rw [Finset.sum_range_succ, inner_partial_sum_11]
  change (1263659 / 7257600) + ((17 / 5) * (1 / (180 / 43) - 1 / (160 / 37)) +
    -11 / 2 * (1 / (180 / 43) ^ 2 - 1 / (160 / 37) ^ 2)) = (581689 / 3225600)
  norm_num

private theorem inner_partial_sum_13 :
    (∑ i ∈ Finset.range 13, innerPieceValue i) = (1828811 / 10080000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_12]
  change (581689 / 3225600) + ((321 / 40) * (1 / (160 / 37) - 1 / (100 / 23)) +
    -31 / 2 * (1 / (160 / 37) ^ 2 - 1 / (100 / 23) ^ 2)) = (1828811 / 10080000)
  norm_num

private theorem inner_partial_sum_14 :
    (∑ i ∈ Finset.range 14, innerPieceValue i) = (3432431 / 18144000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_13]
  change (1828811 / 10080000) + ((55 / 8) * (1 / (100 / 23) - 1 / (9 / 2)) +
    -26 / 2 * (1 / (100 / 23) ^ 2 - 1 / (9 / 2) ^ 2)) = (3432431 / 18144000)
  norm_num

private theorem inner_partial_sum_15 :
    (∑ i ∈ Finset.range 15, innerPieceValue i) = (332467 / 1680000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_14]
  change (3432431 / 18144000) + ((63 / 8) * (1 / (9 / 2) - 1 / (200 / 43)) +
    (-61 / 2) / 2 * (1 / (9 / 2) ^ 2 - 1 / (200 / 43) ^ 2)) = (332467 / 1680000)
  norm_num

private theorem inner_partial_sum_16 :
    (∑ i ∈ Finset.range 16, innerPieceValue i) = (16746439 / 81312000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_15]
  change (332467 / 1680000) + ((93 / 20) * (1 / (200 / 43) - 1 / (110 / 23)) +
    (-31 / 2) / 2 * (1 / (200 / 43) ^ 2 - 1 / (110 / 23) ^ 2)) = (16746439 / 81312000)
  norm_num

private theorem inner_partial_sum_17 :
    (∑ i ∈ Finset.range 17, innerPieceValue i) = (42111623 / 199584000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_16]
  change (16746439 / 81312000) + ((7 / 2) * (1 / (110 / 23) - 1 / (180 / 37)) +
    -10 / 2 * (1 / (110 / 23) ^ 2 - 1 / (180 / 37) ^ 2)) = (42111623 / 199584000)
  norm_num

private theorem inner_partial_sum_18 :
    (∑ i ∈ Finset.range 18, innerPieceValue i) = (4863527 / 22176000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_17]
  change (42111623 / 199584000) + ((107 / 20) * (1 / (180 / 37) - 1 / 5) +
    -19 / 2 * (1 / (180 / 37) ^ 2 - 1 / 5 ^ 2)) = (4863527 / 22176000)
  norm_num

private theorem inner_partial_sum_19 :
    (∑ i ∈ Finset.range 19, innerPieceValue i) = (53226637 / 243936000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_18]
  change (4863527 / 22176000) + ((9 / 2) * (1 / 5 - 1 / (220 / 43)) +
    -24 / 2 * (1 / 5 ^ 2 - 1 / (220 / 43) ^ 2)) = (53226637 / 243936000)
  norm_num

private theorem inner_partial_sum_20 :
    (∑ i ∈ Finset.range 20, innerPieceValue i) = (4826567 / 22176000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_19]
  change (53226637 / 243936000) + ((9 / 2) * (1 / (220 / 43) - 1 / (120 / 23)) +
    -24 / 2 * (1 / (220 / 43) ^ 2 - 1 / (120 / 23) ^ 2)) = (4826567 / 22176000)
  norm_num

private theorem inner_partial_sum_21 :
    (∑ i ∈ Finset.range 21, innerPieceValue i) = (24103267 / 110880000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_20]
  change (4826567 / 22176000) + ((67 / 20) * (1 / (120 / 23) - 1 / (200 / 37)) +
    -18 / 2 * (1 / (120 / 23) ^ 2 - 1 / (200 / 37) ^ 2)) = (24103267 / 110880000)
  norm_num

private theorem inner_partial_sum_22 :
    (∑ i ∈ Finset.range 22, innerPieceValue i) = (53095807 / 243936000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_21]
  change (24103267 / 110880000) + ((319 / 40) * (1 / (200 / 37) - 1 / (11 / 2)) +
    -43 / 2 * (1 / (200 / 37) ^ 2 - 1 / (11 / 2) ^ 2)) = (53095807 / 243936000)
  norm_num

private theorem inner_partial_sum_23 :
    (∑ i ∈ Finset.range 23, innerPieceValue i) = (6453191 / 29568000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_22]
  change (53095807 / 243936000) + ((359 / 40) * (1 / (11 / 2) - 1 / (240 / 43)) +
    (-97 / 2) / 2 * (1 / (11 / 2) ^ 2 - 1 / (240 / 43) ^ 2)) = (6453191 / 29568000)
  norm_num

private theorem inner_partial_sum_24 :
    (∑ i ∈ Finset.range 24, innerPieceValue i) = (205157387 / 936936000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_23]
  change (6453191 / 29568000) + ((23 / 4) * (1 / (240 / 43) - 1 / (130 / 23)) +
    (-61 / 2) / 2 * (1 / (240 / 43) ^ 2 - 1 / (130 / 23) ^ 2)) = (205157387 / 936936000)
  norm_num

private theorem inner_partial_sum_25 :
    (∑ i ∈ Finset.range 25, innerPieceValue i) = (176773789 / 792792000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_24]
  change (205157387 / 936936000) + ((23 / 5) * (1 / (130 / 23) - 1 / (220 / 37)) +
    -24 / 2 * (1 / (130 / 23) ^ 2 - 1 / (220 / 37) ^ 2)) = (176773789 / 792792000)
  norm_num

private theorem inner_partial_sum_26 :
    (∑ i ∈ Finset.range 26, innerPieceValue i) = (488933 / 2184000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_25]
  change (176773789 / 792792000) + ((129 / 20) * (1 / (220 / 37) - 1 / 6) +
    -35 / 2 * (1 / (220 / 37) ^ 2 - 1 / 6 ^ 2)) = (488933 / 2184000)
  norm_num

private theorem inner_partial_sum_27 :
    (∑ i ∈ Finset.range 27, innerPieceValue i) = (18936577 / 85176000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_26]
  change (488933 / 2184000) + ((28 / 5) * (1 / 6 - 1 / (260 / 43)) +
    -41 / 2 * (1 / 6 ^ 2 - 1 / (260 / 43) ^ 2)) = (18936577 / 85176000)
  norm_num

private theorem inner_partial_sum_28 :
    (∑ i ∈ Finset.range 28, innerPieceValue i) = (10138243 / 45864000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_27]
  change (18936577 / 85176000) + ((28 / 5) * (1 / (260 / 43) - 1 / (140 / 23)) +
    -41 / 2 * (1 / (260 / 43) ^ 2 - 1 / (140 / 23) ^ 2)) = (10138243 / 45864000)
  norm_num

private theorem inner_partial_sum_29 :
    (∑ i ∈ Finset.range 29, innerPieceValue i) = (5537711 / 26208000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_28]
  change (10138243 / 45864000) + ((89 / 20) * (1 / (140 / 23) - 1 / (240 / 37)) +
    -34 / 2 * (1 / (140 / 23) ^ 2 - 1 / (240 / 37) ^ 2)) = (5537711 / 26208000)
  norm_num

private theorem inner_partial_sum_30 :
    (∑ i ∈ Finset.range 30, innerPieceValue i) = (71904913 / 340704000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_29]
  change (5537711 / 26208000) + ((363 / 40) * (1 / (240 / 37) - 1 / (13 / 2)) +
    -64 / 2 * (1 / (240 / 37) ^ 2 - 1 / (13 / 2) ^ 2)) = (71904913 / 340704000)
  norm_num

private theorem inner_partial_sum_31 :
    (∑ i ∈ Finset.range 31, innerPieceValue i) = (9669913 / 45864000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_30]
  change (71904913 / 340704000) + ((403 / 40) * (1 / (13 / 2) - 1 / (280 / 43)) +
    (-141 / 2) / 2 * (1 / (13 / 2) ^ 2 - 1 / (280 / 43) ^ 2)) = (9669913 / 45864000)
  norm_num

private theorem inner_partial_sum_32 :
    (∑ i ∈ Finset.range 32, innerPieceValue i) = (27605051 / 131040000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_31]
  change (9669913 / 45864000) + ((137 / 20) * (1 / (280 / 43) - 1 / (150 / 23)) +
    (-99 / 2) / 2 * (1 / (280 / 43) ^ 2 - 1 / (150 / 23) ^ 2)) = (27605051 / 131040000)
  norm_num

private theorem inner_partial_sum_33 :
    (∑ i ∈ Finset.range 33, innerPieceValue i) = (5462479 / 26208000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_32]
  change (27605051 / 131040000) + ((57 / 10) * (1 / (150 / 23) - 1 / (20 / 3)) +
    -42 / 2 * (1 / (150 / 23) ^ 2 - 1 / (20 / 3) ^ 2)) = (5462479 / 26208000)
  norm_num

private theorem inner_partial_sum_34 :
    (∑ i ∈ Finset.range 34, innerPieceValue i) = (21559171 / 104832000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_33]
  change (5462479 / 26208000) + ((69 / 10) * (1 / (20 / 3) - 1 / (160 / 23)) +
    -50 / 2 * (1 / (20 / 3) ^ 2 - 1 / (160 / 23) ^ 2)) = (21559171 / 104832000)
  norm_num

private theorem inner_partial_sum_35 :
    (∑ i ∈ Finset.range 35, innerPieceValue i) = (1683359 / 8190000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_34]
  change (21559171 / 104832000) + ((23 / 4) * (1 / (160 / 23) - 1 / (300 / 43)) +
    -42 / 2 * (1 / (160 / 23) ^ 2 - 1 / (300 / 43) ^ 2)) = (1683359 / 8190000)
  norm_num

private theorem inner_partial_sum_36 :
    (∑ i ∈ Finset.range 36, innerPieceValue i) = (48067 / 234000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_35]
  change (1683359 / 8190000) + ((23 / 4) * (1 / (300 / 43) - 1 / 7) +
    -42 / 2 * (1 / (300 / 43) ^ 2 - 1 / 7 ^ 2)) = (48067 / 234000)
  norm_num

private theorem inner_partial_sum_37 :
    (∑ i ∈ Finset.range 37, innerPieceValue i) = (1242767 / 6084000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_36]
  change (48067 / 234000) + ((49 / 10) * (1 / 7 - 1 / (260 / 37)) +
    -49 / 2 * (1 / 7 ^ 2 - 1 / (260 / 37) ^ 2)) = (1242767 / 6084000)
  norm_num

private theorem inner_partial_sum_38 :
    (∑ i ∈ Finset.range 38, innerPieceValue i) = (25867391 / 135252000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_37]
  change (1242767 / 6084000) + ((27 / 4) * (1 / (260 / 37) - 1 / (170 / 23)) +
    -62 / 2 * (1 / (260 / 37) ^ 2 - 1 / (170 / 23) ^ 2)) = (25867391 / 135252000)
  norm_num

private theorem inner_partial_sum_39 :
    (∑ i ∈ Finset.range 39, innerPieceValue i) = (773023451 / 4073472000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_38]
  change (25867391 / 135252000) + ((28 / 5) * (1 / (170 / 23) - 1 / (320 / 43)) +
    (-107 / 2) / 2 * (1 / (170 / 23) ^ 2 - 1 / (320 / 43) ^ 2)) = (773023451 / 4073472000)
  norm_num

private theorem inner_partial_sum_40 :
    (∑ i ∈ Finset.range 40, innerPieceValue i) = (47896621 / 254592000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_39]
  change (773023451 / 4073472000) + ((19 / 8) * (1 / (320 / 43) - 1 / (15 / 2)) +
    (-59 / 2) / 2 * (1 / (320 / 43) ^ 2 - 1 / (15 / 2) ^ 2)) = (47896621 / 254592000)
  norm_num

private theorem inner_partial_sum_41 :
    (∑ i ∈ Finset.range 41, innerPieceValue i) = (2324118389 / 12475008000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_40]
  change (47896621 / 254592000) + ((27 / 8) * (1 / (15 / 2) - 1 / (280 / 37)) +
    -37 / 2 * (1 / (15 / 2) ^ 2 - 1 / (280 / 37) ^ 2)) = (2324118389 / 12475008000)
  norm_num

private theorem inner_partial_sum_42 :
    (∑ i ∈ Finset.range 42, innerPieceValue i) = (321459427 / 1782144000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_41]
  change (2324118389 / 12475008000) + (8 * (1 / (280 / 37) - 1 / (180 / 23)) +
    -72 / 2 * (1 / (280 / 37) ^ 2 - 1 / (180 / 23) ^ 2)) = (321459427 / 1782144000)
  norm_num

private theorem inner_partial_sum_43 :
    (∑ i ∈ Finset.range 43, innerPieceValue i) = (1806305713 / 10098816000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_42]
  change (321459427 / 1782144000) + ((137 / 20) * (1 / (180 / 23) - 1 / (340 / 43)) +
    -63 / 2 * (1 / (180 / 23) ^ 2 - 1 / (340 / 43) ^ 2)) = (1806305713 / 10098816000)
  norm_num

private theorem inner_partial_sum_44 :
    (∑ i ∈ Finset.range 44, innerPieceValue i) = (105317369 / 594048000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_43]
  change (1806305713 / 10098816000) + ((137 / 20) * (1 / (340 / 43) - 1 / 8) +
    -63 / 2 * (1 / (340 / 43) ^ 2 - 1 / 8 ^ 2)) = (105317369 / 594048000)
  norm_num

private theorem inner_partial_sum_45 :
    (∑ i ∈ Finset.range 45, innerPieceValue i) = (1537942031 / 8910720000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_44]
  change (105317369 / 594048000) + (6 * (1 / 8 - 1 / (300 / 37)) +
    -71 / 2 * (1 / 8 ^ 2 - 1 / (300 / 37) ^ 2)) = (1537942031 / 8910720000)
  norm_num

private theorem inner_partial_sum_46 :
    (∑ i ∈ Finset.range 46, innerPieceValue i) = (2380854663 / 14296755200) := by
  rw [Finset.sum_range_succ, inner_partial_sum_45]
  change (1537942031 / 8910720000) + ((157 / 20) * (1 / (300 / 37) - 1 / (190 / 23)) +
    -86 / 2 * (1 / (300 / 37) ^ 2 - 1 / (190 / 23) ^ 2)) = (2380854663 / 14296755200)
  norm_num

private theorem inner_partial_sum_47 :
    (∑ i ∈ Finset.range 47, innerPieceValue i) = (1100556809 / 6772147200) := by
  rw [Finset.sum_range_succ, inner_partial_sum_46]
  change (2380854663 / 14296755200) + ((67 / 10) * (1 / (190 / 23) - 1 / (360 / 43)) +
    (-153 / 2) / 2 * (1 / (190 / 23) ^ 2 - 1 / (360 / 43) ^ 2)) = (1100556809 / 6772147200)
  norm_num

private theorem inner_partial_sum_48 :
    (∑ i ∈ Finset.range 48, innerPieceValue i) = (6071429023 / 38375500800) := by
  rw [Finset.sum_range_succ, inner_partial_sum_47]
  change (1100556809 / 6772147200) + ((139 / 40) * (1 / (360 / 43) - 1 / (17 / 2)) +
    (-99 / 2) / 2 * (1 / (360 / 43) ^ 2 - 1 / (17 / 2) ^ 2)) = (6071429023 / 38375500800)
  norm_num

private theorem inner_partial_sum_49 :
    (∑ i ∈ Finset.range 49, innerPieceValue i) = (1386762179 / 9029529600) := by
  rw [Finset.sum_range_succ, inner_partial_sum_48]
  change (6071429023 / 38375500800) + ((179 / 40) * (1 / (17 / 2) - 1 / (320 / 37)) +
    -58 / 2 * (1 / (17 / 2) ^ 2 - 1 / (320 / 37) ^ 2)) = (1386762179 / 9029529600)
  norm_num

private theorem inner_partial_sum_50 :
    (∑ i ∈ Finset.range 50, innerPieceValue i) = (4294822027 / 28217280000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_49]
  change (1386762179 / 9029529600) + ((91 / 10) * (1 / (320 / 37) - 1 / (200 / 23)) +
    -98 / 2 * (1 / (320 / 37) ^ 2 - 1 / (200 / 23) ^ 2)) = (4294822027 / 28217280000)
  norm_num

private theorem inner_partial_sum_51 :
    (∑ i ∈ Finset.range 51, innerPieceValue i) = (15907712813 / 107225664000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_50]
  change (4294822027 / 28217280000) + ((159 / 20) * (1 / (200 / 23) - 1 / (380 / 43)) +
    -88 / 2 * (1 / (200 / 23) ^ 2 - 1 / (380 / 43) ^ 2)) = (15907712813 / 107225664000)
  norm_num

private theorem inner_partial_sum_52 :
    (∑ i ∈ Finset.range 52, innerPieceValue i) = (22007571589 / 152373312000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_51]
  change (15907712813 / 107225664000) + ((159 / 20) * (1 / (380 / 43) - 1 / 9) +
    -88 / 2 * (1 / (380 / 43) ^ 2 - 1 / 9 ^ 2)) = (22007571589 / 152373312000)
  norm_num

private theorem inner_partial_sum_53 :
    (∑ i ∈ Finset.range 53, innerPieceValue i) = (16439636107 / 118512576000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_52]
  change (22007571589 / 152373312000) + ((71 / 10) * (1 / 9 - 1 / (210 / 23)) +
    -97 / 2 * (1 / 9 ^ 2 - 1 / (210 / 23) ^ 2)) = (16439636107 / 118512576000)
  norm_num

private theorem inner_partial_sum_54 :
    (∑ i ∈ Finset.range 54, innerPieceValue i) = (622550859 / 4568512000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_53]
  change (16439636107 / 118512576000) + ((119 / 20) * (1 / (210 / 23) - 1 / (340 / 37)) +
    (-173 / 2) / 2 * (1 / (210 / 23) ^ 2 - 1 / (340 / 37) ^ 2)) = (622550859 / 4568512000)
  norm_num

private theorem inner_partial_sum_55 :
    (∑ i ∈ Finset.range 55, innerPieceValue i) = (354131967 / 2687360000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_54]
  change (622550859 / 4568512000) + ((39 / 5) * (1 / (340 / 37) - 1 / (400 / 43)) +
    (-207 / 2) / 2 * (1 / (340 / 37) ^ 2 - 1 / (400 / 43) ^ 2)) = (354131967 / 2687360000)
  norm_num

private theorem inner_partial_sum_56 :
    (∑ i ∈ Finset.range 56, innerPieceValue i) = (635799579 / 5105984000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_55]
  change (354131967 / 2687360000) + ((183 / 40) * (1 / (400 / 43) - 1 / (19 / 2)) +
    (-147 / 2) / 2 * (1 / (400 / 43) ^ 2 - 1 / (19 / 2) ^ 2)) = (635799579 / 5105984000)
  norm_num

private theorem inner_partial_sum_57 :
    (∑ i ∈ Finset.range 57, innerPieceValue i) = (3975944721 / 32517056000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_56]
  change (635799579 / 5105984000) + ((223 / 40) * (1 / (19 / 2) - 1 / (220 / 23)) +
    -83 / 2 * (1 / (19 / 2) ^ 2 - 1 / (220 / 23) ^ 2)) = (3975944721 / 32517056000)
  norm_num

private theorem inner_partial_sum_58 :
    (∑ i ∈ Finset.range 58, innerPieceValue i) = (3110142259 / 26604864000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_57]
  change (3975944721 / 32517056000) + ((177 / 40) * (1 / (220 / 23) - 1 / (360 / 37)) +
    -72 / 2 * (1 / (220 / 23) ^ 2 - 1 / (360 / 37) ^ 2)) = (3110142259 / 26604864000)
  norm_num

private theorem inner_partial_sum_59 :
    (∑ i ∈ Finset.range 59, innerPieceValue i) = (150869962351 / 1303638336000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_58]
  change (3110142259 / 26604864000) + ((181 / 20) * (1 / (360 / 37) - 1 / (420 / 43)) +
    -117 / 2 * (1 / (360 / 37) ^ 2 - 1 / (420 / 43) ^ 2)) = (150869962351 / 1303638336000)
  norm_num

private theorem inner_partial_sum_60 :
    (∑ i ∈ Finset.range 60, innerPieceValue i) = (2902291759 / 26604864000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_59]
  change (150869962351 / 1303638336000) + ((181 / 20) * (1 / (420 / 43) - 1 / 10) +
    -117 / 2 * (1 / (420 / 43) ^ 2 - 1 / 10 ^ 2)) = (2902291759 / 26604864000)
  norm_num

private theorem inner_partial_sum_61 :
    (∑ i ∈ Finset.range 61, innerPieceValue i) = (29018325629 / 292653504000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_60]
  change (2902291759 / 26604864000) + ((69 / 10) * (1 / 10 - 1 / (440 / 43)) +
    -114 / 2 * (1 / 10 ^ 2 - 1 / (440 / 43) ^ 2)) = (29018325629 / 292653504000)
  norm_num

private theorem inner_partial_sum_62 :
    (∑ i ∈ Finset.range 62, innerPieceValue i) = (49355911441 / 505492416000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_61]
  change (29018325629 / 292653504000) + ((147 / 40) * (1 / (440 / 43) - 1 / (380 / 37)) +
    -81 / 2 * (1 / (440 / 43) ^ 2 - 1 / (380 / 37) ^ 2)) = (49355911441 / 505492416000)
  norm_num

private theorem inner_partial_sum_63 :
    (∑ i ∈ Finset.range 63, innerPieceValue i) = (809599753 / 8868288000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_62]
  change (49355911441 / 505492416000) + ((221 / 40) * (1 / (380 / 37) - 1 / (240 / 23)) +
    -100 / 2 * (1 / (380 / 37) ^ 2 - 1 / (240 / 23) ^ 2)) = (809599753 / 8868288000)
  norm_num

private theorem inner_partial_sum_64 :
    (∑ i ∈ Finset.range 64, innerPieceValue i) = (38627440277 / 434546112000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_63]
  change (809599753 / 8868288000) + ((35 / 8) * (1 / (240 / 23) - 1 / (21 / 2)) +
    -88 / 2 * (1 / (240 / 23) ^ 2 - 1 / (21 / 2) ^ 2)) = (38627440277 / 434546112000)
  norm_num

private theorem inner_partial_sum_65 :
    (∑ i ∈ Finset.range 65, innerPieceValue i) = (8077887148897 / 98517811392000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_64]
  change (38627440277 / 434546112000) + ((43 / 8) * (1 / (21 / 2) - 1 / (460 / 43)) +
    (-197 / 2) / 2 * (1 / (21 / 2) ^ 2 - 1 / (460 / 43) ^ 2)) = (8077887148897 / 98517811392000)
  norm_num

private theorem inner_partial_sum_66 :
    (∑ i ∈ Finset.range 66, innerPieceValue i) = (145806399481 / 1862340480000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_65]
  change (8077887148897 / 98517811392000) + ((43 / 8) * (1 / (460 / 43) - 1 / (400 / 37)) +
    (-197 / 2) / 2 * (1 / (460 / 43) ^ 2 - 1 / (400 / 37) ^ 2)) = (145806399481 / 1862340480000)
  norm_num

private theorem inner_partial_sum_67 :
    (∑ i ∈ Finset.range 67, innerPieceValue i) = (1779523554587 / 23279256000000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_66]
  change (145806399481 / 1862340480000) + (10 * (1 / (400 / 37) - 1 / (250 / 23)) +
    (-297 / 2) / 2 * (1 / (400 / 37) ^ 2 - 1 / (250 / 23) ^ 2)) = (1779523554587 / 23279256000000)
  norm_num

private theorem inner_partial_sum_68 :
    (∑ i ∈ Finset.range 68, innerPieceValue i) = (742899929809 / 10242872640000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_67]
  change (1779523554587 / 23279256000000) + ((177 / 20) * (1 / (250 / 23) - 1 / 11) +
    -136 / 2 * (1 / (250 / 23) ^ 2 - 1 / 11 ^ 2)) = (742899929809 / 10242872640000)
  norm_num

private theorem inner_partial_sum_69 :
    (∑ i ∈ Finset.range 69, innerPieceValue i) = (244140840701 / 3724680960000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_68]
  change (742899929809 / 10242872640000) + (8 * (1 / 11 - 1 / (480 / 43)) +
    -147 / 2 * (1 / 11 ^ 2 - 1 / (480 / 43) ^ 2)) = (244140840701 / 3724680960000)
  norm_num

private theorem inner_partial_sum_70 :
    (∑ i ∈ Finset.range 70, innerPieceValue i) = (45257113067 / 756575820000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_69]
  change (244140840701 / 3724680960000) + ((191 / 40) * (1 / (480 / 43) - 1 / (260 / 23)) +
    -111 / 2 * (1 / (480 / 43) ^ 2 - 1 / (260 / 23) ^ 2)) = (45257113067 / 756575820000)
  norm_num

private theorem inner_partial_sum_71 :
    (∑ i ∈ Finset.range 71, innerPieceValue i) = (3374166109 / 58198140000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_70]
  change (45257113067 / 756575820000) + ((29 / 8) * (1 / (260 / 23) - 1 / (420 / 37)) +
    -98 / 2 * (1 / (260 / 23) ^ 2 - 1 / (420 / 37) ^ 2)) = (3374166109 / 58198140000)
  norm_num

private theorem inner_partial_sum_72 :
    (∑ i ∈ Finset.range 72, innerPieceValue i) = (1611729740561 / 30786816060000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_71]
  change (3374166109 / 58198140000) + ((219 / 40) * (1 / (420 / 37) - 1 / (23 / 2)) +
    -119 / 2 * (1 / (420 / 37) ^ 2 - 1 / (23 / 2) ^ 2)) = (1611729740561 / 30786816060000)
  norm_num

private theorem inner_partial_sum_73 :
    (∑ i ∈ Finset.range 73, innerPieceValue i) = (3195807504629 / 66927861000000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_72]
  change (1611729740561 / 30786816060000) + ((259 / 40) * (1 / (23 / 2) - 1 / (500 / 43)) +
    (-261 / 2) / 2 * (1 / (23 / 2) ^ 2 - 1 / (500 / 43) ^ 2)) = (3195807504629 / 66927861000000)
  norm_num

private theorem inner_partial_sum_74 :
    (∑ i ∈ Finset.range 74, innerPieceValue i) = (529160461763 / 12047014980000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_73]
  change (3195807504629 / 66927861000000) + ((259 / 40) * (1 / (500 / 43) - 1 / (270 / 23)) +
    (-261 / 2) / 2 * (1 / (500 / 43) ^ 2 - 1 / (270 / 23) ^ 2)) = (529160461763 / 12047014980000)
  norm_num

private theorem inner_partial_sum_75 :
    (∑ i ∈ Finset.range 75, innerPieceValue i) = (6875944213399 / 176689553040000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_74]
  change (529160461763 / 12047014980000) + ((213 / 40) * (1 / (270 / 23) - 1 / (440 / 37)) +
    -117 / 2 * (1 / (270 / 23) ^ 2 - 1 / (440 / 37) ^ 2)) = (6875944213399 / 176689553040000)
  norm_num

private theorem inner_partial_sum_76 :
    (∑ i ∈ Finset.range 76, innerPieceValue i) = (570953551109 / 16062686640000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_75]
  change (6875944213399 / 176689553040000) + ((199 / 20) * (1 / (440 / 37) - 1 / 12) +
    -172 / 2 * (1 / (440 / 37) ^ 2 - 1 / 12 ^ 2)) = (570953551109 / 16062686640000)
  norm_num

private theorem inner_partial_sum_77 :
    (∑ i ∈ Finset.range 77, innerPieceValue i) = (6595922886017 / 208814926320000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_76]
  change (570953551109 / 16062686640000) + ((91 / 10) * (1 / 12 - 1 / (520 / 43)) +
    -184 / 2 * (1 / 12 ^ 2 - 1 / (520 / 43) ^ 2)) = (6595922886017 / 208814926320000)
  norm_num

private theorem inner_partial_sum_78 :
    (∑ i ∈ Finset.range 78, innerPieceValue i) = (3176305988663 / 112438806480000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_77]
  change (6595922886017 / 208814926320000) + ((47 / 8) * (1 / (520 / 43) - 1 / (280 / 23)) +
    -145 / 2 * (1 / (520 / 43) ^ 2 - 1 / (280 / 23) ^ 2)) = (3176305988663 / 112438806480000)
  norm_num

private theorem inner_partial_sum_79 :
    (∑ i ∈ Finset.range 79, innerPieceValue i) = (478449408113 / 26388699480000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_78]
  change (3176305988663 / 112438806480000) + ((189 / 40) * (1 / (280 / 23) - 1 / (460 / 37)) +
    -131 / 2 * (1 / (280 / 23) ^ 2 - 1 / (460 / 37) ^ 2)) = (478449408113 / 26388699480000)
  norm_num

private theorem inner_partial_sum_80 :
    (∑ i ∈ Finset.range 80, innerPieceValue i) = (17919605149 / 1147334760000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_79]
  change (478449408113 / 26388699480000) + ((263 / 40) * (1 / (460 / 37) - 1 / (25 / 2)) +
    -154 / 2 * (1 / (460 / 37) ^ 2 - 1 / (25 / 2) ^ 2)) = (17919605149 / 1147334760000)
  norm_num

private theorem inner_partial_sum_81 :
    (∑ i ∈ Finset.range 81, innerPieceValue i) = (11618575517 / 860501070000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_80]
  change (17919605149 / 1147334760000) + ((303 / 40) * (1 / (25 / 2) - 1 / (540 / 43)) +
    (-333 / 2) / 2 * (1 / (25 / 2) ^ 2 - 1 / (540 / 43) ^ 2)) = (11618575517 / 860501070000)
  norm_num

private theorem inner_partial_sum_82 :
    (∑ i ∈ Finset.range 82, innerPieceValue i) = (11285560024021 / 964908533160000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_81]
  change (11618575517 / 860501070000) + ((303 / 40) * (1 / (540 / 43) - 1 / (290 / 23)) +
    (-333 / 2) / 2 * (1 / (540 / 43) ^ 2 - 1 / (290 / 23) ^ 2)) = (11285560024021 / 964908533160000)
  norm_num

private theorem inner_partial_sum_83 :
    (∑ i ∈ Finset.range 83, innerPieceValue i) = (-3872453569 / 8318177010000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_82]
  change (11285560024021 / 964908533160000) + ((257 / 40) * (1 / (290 / 23) - 1 / (480 / 37)) +
    -152 / 2 * (1 / (290 / 23) ^ 2 - 1 / (480 / 37) ^ 2)) = (-3872453569 / 8318177010000)
  norm_num

private theorem inner_partial_sum_84 :
    (∑ i ∈ Finset.range 84, innerPieceValue i) = (-4535988527729 / 3460361636160000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_83]
  change (-3872453569 / 8318177010000) + ((221 / 20) * (1 / (480 / 37) - 1 / 13) +
    -212 / 2 * (1 / (480 / 37) ^ 2 - 1 / 13 ^ 2)) = (-4535988527729 / 3460361636160000)
  norm_num

private theorem inner_partial_sum_85 :
    (∑ i ∈ Finset.range 85, innerPieceValue i) = (-1862730944387 / 815181346980000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_84]
  change (-4535988527729 / 3460361636160000) + ((51 / 5) * (1 / 13 - 1 / (560 / 43)) +
    -225 / 2 * (1 / 13 ^ 2 - 1 / (560 / 43) ^ 2)) = (-1862730944387 / 815181346980000)
  norm_num

private theorem inner_partial_sum_86 :
    (∑ i ∈ Finset.range 86, innerPieceValue i) = (-1165002666109 / 372654330048000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_85]
  change (-1862730944387 / 815181346980000) + ((279 / 40) * (1 / (560 / 43) - 1 / (300 / 23)) +
    -183 / 2 * (1 / (560 / 43) ^ 2 - 1 / (300 / 23) ^ 2)) = (-1165002666109 / 372654330048000)
  norm_num

private theorem inner_partial_sum_87 :
    (∑ i ∈ Finset.range 87, innerPieceValue i) = (-27299219099561 / 1863271650240000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_86]
  change (-1165002666109 / 372654330048000) + ((233 / 40) * (1 / (300 / 23) - 1 / (40 / 3)) +
    -168 / 2 * (1 / (300 / 23) ^ 2 - 1 / (40 / 3) ^ 2)) = (-27299219099561 / 1863271650240000)
  norm_num

private theorem inner_partial_sum_88 :
    (∑ i ∈ Finset.range 88, innerPieceValue i) = (-19881957772141121 / 1790604055880640000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_87]
  change (-27299219099561 / 1863271650240000) + ((145 / 8) * (1 / (40 / 3) - 1 / (310 / 23)) +
    -184 / 2 * (1 / (40 / 3) ^ 2 - 1 / (310 / 23) ^ 2)) = (-19881957772141121 / 1790604055880640000)
  norm_num

private theorem inner_partial_sum_89 :
    (∑ i ∈ Finset.range 89, innerPieceValue i) = (-18182057508830539 / 1675081213565760000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_88]
  change (-19881957772141121 / 1790604055880640000) + ((679 / 40) * (1 / (310 / 23) - 1 / (580 / 43)) +
    (-337 / 2) / 2 * (1 / (310 / 23) ^ 2 - 1 / (580 / 43) ^ 2)) = (-18182057508830539 / 1675081213565760000)
  norm_num

private theorem inner_partial_sum_90 :
    (∑ i ∈ Finset.range 90, innerPieceValue i) = (-16481154814890757 / 1559558371250880000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_89]
  change (-18182057508830539 / 1675081213565760000) + ((679 / 40) * (1 / (580 / 43) - 1 / (27 / 2)) +
    (-337 / 2) / 2 * (1 / (580 / 43) ^ 2 - 1 / (27 / 2) ^ 2)) = (-16481154814890757 / 1559558371250880000)
  norm_num

private theorem inner_partial_sum_91 :
    (∑ i ∈ Finset.range 91, innerPieceValue i) = (-547368726821237 / 53482797368000000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_90]
  change (-16481154814890757 / 1559558371250880000) + ((719 / 40) * (1 / (27 / 2) - 1 / (500 / 37)) +
    -182 / 2 * (1 / (27 / 2) ^ 2 - 1 / (500 / 37) ^ 2)) = (-547368726821237 / 53482797368000000)
  norm_num

private theorem inner_partial_sum_92 :
    (∑ i ∈ Finset.range 92, innerPieceValue i) = (-6494602107759 / 34228990315520000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_91]
  change (-547368726821237 / 53482797368000000) + ((793 / 40) * (1 / (500 / 37) - 1 / (320 / 23)) +
    -207 / 2 * (1 / (500 / 37) ^ 2 - 1 / (320 / 23) ^ 2)) = (-6494602107759 / 34228990315520000)
  norm_num

private theorem inner_partial_sum_93 :
    (∑ i ∈ Finset.range 93, innerPieceValue i) = (6355291472 / 7521018379875) := by
  rw [Finset.sum_range_succ, inner_partial_sum_92]
  change (-6494602107759 / 34228990315520000) + ((747 / 40) * (1 / (320 / 23) - 1 / (600 / 43)) +
    -191 / 2 * (1 / (320 / 23) ^ 2 - 1 / (600 / 43) ^ 2)) = (6355291472 / 7521018379875)
  norm_num

private theorem inner_partial_sum_94 :
    (∑ i ∈ Finset.range 94, innerPieceValue i) = (3812015306609 / 1871897907880000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_93]
  change (6355291472 / 7521018379875) + ((309 / 20) * (1 / (600 / 43) - 1 / 14) +
    -146 / 2 * (1 / (600 / 43) ^ 2 - 1 / 14 ^ 2)) = (3812015306609 / 1871897907880000)
  norm_num

private theorem inner_partial_sum_95 :
    (∑ i ∈ Finset.range 95, innerPieceValue i) = (10129319814931 / 3476381828920000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_94]
  change (3812015306609 / 1871897907880000) + ((73 / 5) * (1 / 14 - 1 / (520 / 37)) +
    -160 / 2 * (1 / 14 ^ 2 - 1 / (520 / 37) ^ 2)) = (10129319814931 / 3476381828920000)
  norm_num

private theorem inner_partial_sum_96 :
    (∑ i ∈ Finset.range 96, innerPieceValue i) = (138316892681717 / 17649323131440000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_95]
  change (10129319814931 / 3476381828920000) + ((769 / 40) * (1 / (520 / 37) - 1 / (330 / 23)) +
    -225 / 2 * (1 / (520 / 37) ^ 2 - 1 / (330 / 23) ^ 2)) = (138316892681717 / 17649323131440000)
  norm_num

private theorem inner_partial_sum_97 :
    (∑ i ∈ Finset.range 97, innerPieceValue i) = (40973121188137 / 4521727413840000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_96]
  change (138316892681717 / 17649323131440000) + ((723 / 40) * (1 / (330 / 23) - 1 / (620 / 43)) +
    (-417 / 2) / 2 * (1 / (330 / 23) ^ 2 - 1 / (620 / 43) ^ 2)) = (40973121188137 / 4521727413840000)
  norm_num

private theorem inner_partial_sum_98 :
    (∑ i ∈ Finset.range 98, innerPieceValue i) = (44349030780233 / 4230003064560000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_97]
  change (40973121188137 / 4521727413840000) + ((723 / 40) * (1 / (620 / 43) - 1 / (29 / 2)) +
    (-417 / 2) / 2 * (1 / (620 / 43) ^ 2 - 1 / (29 / 2) ^ 2)) = (44349030780233 / 4230003064560000)
  norm_num

private theorem inner_partial_sum_99 :
    (∑ i ∈ Finset.range 99, innerPieceValue i) = (430957159001711 / 35444508437520000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_98]
  change (44349030780233 / 4230003064560000) + ((763 / 40) * (1 / (29 / 2) - 1 / (540 / 37)) +
    -223 / 2 * (1 / (29 / 2) ^ 2 - 1 / (540 / 37) ^ 2)) = (430957159001711 / 35444508437520000)
  norm_num

private theorem inner_partial_sum_100 :
    (∑ i ∈ Finset.range 100, innerPieceValue i) = (347275409950381 / 22316912719920000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_99]
  change (430957159001711 / 35444508437520000) + ((837 / 40) * (1 / (540 / 37) - 1 / (340 / 23)) +
    -250 / 2 * (1 / (540 / 37) ^ 2 - 1 / (340 / 23) ^ 2)) = (347275409950381 / 22316912719920000)
  norm_num

private theorem inner_partial_sum_101 :
    (∑ i ∈ Finset.range 101, innerPieceValue i) = (5857641039199583 / 336066450370560000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_100]
  change (347275409950381 / 22316912719920000) + ((791 / 40) * (1 / (340 / 23) - 1 / (640 / 43)) +
    -233 / 2 * (1 / (340 / 23) ^ 2 - 1 / (640 / 43) ^ 2)) = (5857641039199583 / 336066450370560000)
  norm_num

private theorem inner_partial_sum_102 :
    (∑ i ∈ Finset.range 102, innerPieceValue i) = (411704436619163 / 21004153148160000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_101]
  change (5857641039199583 / 336066450370560000) + ((331 / 20) * (1 / (640 / 43) - 1 / 15) +
    -185 / 2 * (1 / (640 / 43) ^ 2 - 1 / 15 ^ 2)) = (411704436619163 / 21004153148160000)
  norm_num

private theorem inner_partial_sum_103 :
    (∑ i ∈ Finset.range 103, innerPieceValue i) = (3094264707702941 / 147029072037120000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_102]
  change (411704436619163 / 21004153148160000) + ((157 / 10) * (1 / 15 - 1 / (560 / 37)) +
    -200 / 2 * (1 / 15 ^ 2 - 1 / (560 / 37) ^ 2)) = (3094264707702941 / 147029072037120000)
  norm_num

private theorem inner_partial_sum_104 :
    (∑ i ∈ Finset.range 104, innerPieceValue i) = (3227322267154901 / 147029072037120000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_103]
  change (3094264707702941 / 147029072037120000) + ((813 / 40) * (1 / (560 / 37) - 1 / (350 / 23)) +
    -270 / 2 * (1 / (560 / 37) ^ 2 - 1 / (350 / 23) ^ 2)) = (3227322267154901 / 147029072037120000)
  norm_num

private theorem inner_partial_sum_105 :
    (∑ i ∈ Finset.range 105, innerPieceValue i) = (59581386442537163 / 2541502530927360000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_104]
  change (3227322267154901 / 147029072037120000) + ((767 / 40) * (1 / (350 / 23) - 1 / (660 / 43)) +
    (-505 / 2) / 2 * (1 / (350 / 23) ^ 2 - 1 / (660 / 43) ^ 2)) = (59581386442537163 / 2541502530927360000)
  norm_num

private theorem inner_partial_sum_106 :
    (∑ i ∈ Finset.range 106, innerPieceValue i) = (16424908746219293 / 651128747592960000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_105]
  change (59581386442537163 / 2541502530927360000) + ((767 / 40) * (1 / (660 / 43) - 1 / (31 / 2)) +
    (-505 / 2) / 2 * (1 / (660 / 43) ^ 2 - 1 / (31 / 2) ^ 2)) = (16424908746219293 / 651128747592960000)
  norm_num

private theorem inner_partial_sum_107 :
    (∑ i ∈ Finset.range 107, innerPieceValue i) = (1706843121663209 / 63012459444480000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_106]
  change (16424908746219293 / 651128747592960000) + ((807 / 40) * (1 / (31 / 2) - 1 / (360 / 23)) +
    -268 / 2 * (1 / (31 / 2) ^ 2 - 1 / (360 / 23) ^ 2)) = (1706843121663209 / 63012459444480000)
  norm_num

private theorem inner_partial_sum_108 :
    (∑ i ∈ Finset.range 108, innerPieceValue i) = (16678296005188087 / 609120441296640000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_107]
  change (1706843121663209 / 63012459444480000) + ((761 / 40) * (1 / (360 / 23) - 1 / (580 / 37)) +
    -250 / 2 * (1 / (360 / 23) ^ 2 - 1 / (580 / 37) ^ 2)) = (16678296005188087 / 609120441296640000)
  norm_num

private theorem inner_partial_sum_109 :
    (∑ i ∈ Finset.range 109, innerPieceValue i) = (10405244655250051 / 357070603518720000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_108]
  change (16678296005188087 / 609120441296640000) + ((167 / 8) * (1 / (580 / 37) - 1 / (680 / 43)) +
    -279 / 2 * (1 / (580 / 37) ^ 2 - 1 / (680 / 43) ^ 2)) = (10405244655250051 / 357070603518720000)
  norm_num

private theorem inner_partial_sum_110 :
    (∑ i ∈ Finset.range 110, innerPieceValue i) = (663289007996003 / 21004153148160000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_109]
  change (10405244655250051 / 357070603518720000) + ((353 / 20) * (1 / (680 / 43) - 1 / 16) +
    -228 / 2 * (1 / (680 / 43) ^ 2 - 1 / 16 ^ 2)) = (663289007996003 / 21004153148160000)
  norm_num

private theorem inner_partial_sum_111 :
    (∑ i ∈ Finset.range 111, innerPieceValue i) = (923500395904002107 / 28754685659831040000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_110]
  change (663289007996003 / 21004153148160000) + ((84 / 5) * (1 / 16 - 1 / (370 / 23)) +
    -244 / 2 * (1 / 16 ^ 2 - 1 / (370 / 23) ^ 2)) = (923500395904002107 / 28754685659831040000)
  norm_num

private theorem inner_partial_sum_112 :
    (∑ i ∈ Finset.range 112, innerPieceValue i) = (25609594035043943 / 777153666481920000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_111]
  change (923500395904002107 / 28754685659831040000) + ((313 / 20) * (1 / (370 / 23) - 1 / (600 / 37)) +
    (-451 / 2) / 2 * (1 / (370 / 23) ^ 2 - 1 / (600 / 37) ^ 2)) = (25609594035043943 / 777153666481920000)
  norm_num

private theorem inner_partial_sum_113 :
    (∑ i ∈ Finset.range 113, innerPieceValue i) = (181572637023959273 / 5440075665373440000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_112]
  change (25609594035043943 / 777153666481920000) + ((811 / 40) * (1 / (600 / 37) - 1 / (700 / 43)) +
    (-601 / 2) / 2 * (1 / (600 / 37) ^ 2 - 1 / (700 / 43) ^ 2)) = (181572637023959273 / 5440075665373440000)
  norm_num

private theorem inner_partial_sum_114 :
    (∑ i ∈ Finset.range 114, innerPieceValue i) = (3288608185470880631 / 94035593644312320000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_113]
  change (181572637023959273 / 5440075665373440000) + ((811 / 40) * (1 / (700 / 43) - 1 / (33 / 2)) +
    (-601 / 2) / 2 * (1 / (700 / 43) ^ 2 - 1 / (33 / 2) ^ 2)) = (3288608185470880631 / 94035593644312320000)
  norm_num

private theorem inner_partial_sum_115 :
    (∑ i ∈ Finset.range 115, innerPieceValue i) = (5707206507596333599 / 162425116294721280000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_114]
  change (3288608185470880631 / 94035593644312320000) + ((851 / 40) * (1 / (33 / 2) - 1 / (380 / 23)) +
    -317 / 2 * (1 / (33 / 2) ^ 2 - 1 / (380 / 23) ^ 2)) = (5707206507596333599 / 162425116294721280000)
  norm_num

private theorem inner_partial_sum_116 :
    (∑ i ∈ Finset.range 116, innerPieceValue i) = (310127401715264389 / 8548690331301120000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_115]
  change (5707206507596333599 / 162425116294721280000) + ((161 / 8) * (1 / (380 / 23) - 1 / (50 / 3)) +
    -298 / 2 * (1 / (380 / 23) ^ 2 - 1 / (50 / 3) ^ 2)) = (310127401715264389 / 8548690331301120000)
  norm_num

private theorem inner_partial_sum_117 :
    (∑ i ∈ Finset.range 117, innerPieceValue i) = (315555919018815731 / 8548690331301120000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_116]
  change (310127401715264389 / 8548690331301120000) + ((799 / 40) * (1 / (50 / 3) - 1 / (720 / 43)) +
    (-591 / 2) / 2 * (1 / (50 / 3) ^ 2 - 1 / (720 / 43) ^ 2)) = (315555919018815731 / 8548690331301120000)
  norm_num

private theorem inner_partial_sum_118 :
    (∑ i ∈ Finset.range 118, innerPieceValue i) = (9809927604509515411 / 265009400270334720000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_117]
  change (315555919018815731 / 8548690331301120000) + ((67 / 4) * (1 / (720 / 43) - 1 / (620 / 37)) +
    (-483 / 2) / 2 * (1 / (720 / 43) ^ 2 - 1 / (620 / 37) ^ 2)) = (9809927604509515411 / 265009400270334720000)
  norm_num

private theorem inner_partial_sum_119 :
    (∑ i ∈ Finset.range 119, innerPieceValue i) = (4303992980933782153 / 111132974306914560000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_118]
  change (9809927604509515411 / 265009400270334720000) + ((93 / 5) * (1 / (620 / 37) - 1 / (390 / 23)) +
    (-545 / 2) / 2 * (1 / (620 / 37) ^ 2 - 1 / (390 / 23) ^ 2)) = (4303992980933782153 / 111132974306914560000)
  norm_num

private theorem inner_partial_sum_120 :
    (∑ i ∈ Finset.range 120, innerPieceValue i) = (5684162388119036477 / 145327735632119040000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_119]
  change (4303992980933782153 / 111132974306914560000) + ((349 / 20) * (1 / (390 / 23) - 1 / 17) +
    -253 / 2 * (1 / (390 / 23) ^ 2 - 1 / 17 ^ 2)) = (5684162388119036477 / 145327735632119040000)
  norm_num

private theorem inner_partial_sum_121 :
    (∑ i ∈ Finset.range 121, innerPieceValue i) = (12555663195326239297 / 316301542258141440000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_120]
  change (5684162388119036477 / 145327735632119040000) + ((83 / 5) * (1 / 17 - 1 / (740 / 43)) +
    -270 / 2 * (1 / 17 ^ 2 - 1 / (740 / 43) ^ 2)) = (12555663195326239297 / 316301542258141440000)
  norm_num

private theorem inner_partial_sum_122 :
    (∑ i ∈ Finset.range 122, innerPieceValue i) = (2733958174246260623 / 68389522650408960000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_121]
  change (12555663195326239297 / 316301542258141440000) + ((83 / 5) * (1 / (740 / 43) - 1 / (640 / 37)) +
    -270 / 2 * (1 / (740 / 43) ^ 2 - 1 / (640 / 37) ^ 2)) = (2733958174246260623 / 68389522650408960000)
  norm_num

private theorem inner_partial_sum_123 :
    (∑ i ∈ Finset.range 123, innerPieceValue i) = (172268644150069133 / 4274345165650560000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_122]
  change (2733958174246260623 / 68389522650408960000) + ((849 / 40) * (1 / (640 / 37) - 1 / (400 / 23)) +
    -350 / 2 * (1 / (640 / 37) ^ 2 - 1 / (400 / 23) ^ 2)) = (172268644150069133 / 4274345165650560000)
  norm_num

private theorem inner_partial_sum_124 :
    (∑ i ∈ Finset.range 124, innerPieceValue i) = (1218264660892033991 / 29920416159553920000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_123]
  change (172268644150069133 / 4274345165650560000) + ((803 / 40) * (1 / (400 / 23) - 1 / (35 / 2)) +
    -330 / 2 * (1 / (400 / 23) ^ 2 - 1 / (35 / 2) ^ 2)) = (1218264660892033991 / 29920416159553920000)
  norm_num

private theorem inner_partial_sum_125 :
    (∑ i ∈ Finset.range 125, innerPieceValue i) = (3366979142827744247 / 81212558147360640000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_124]
  change (1218264660892033991 / 29920416159553920000) + ((843 / 40) * (1 / (35 / 2) - 1 / (760 / 43)) +
    (-695 / 2) / 2 * (1 / (35 / 2) ^ 2 - 1 / (760 / 43) ^ 2)) = (3366979142827744247 / 81212558147360640000)
  norm_num

private theorem inner_partial_sum_126 :
    (∑ i ∈ Finset.range 126, innerPieceValue i) = (303021066443711433353 / 7185174223458591360000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_125]
  change (3366979142827744247 / 81212558147360640000) + ((357 / 20) * (1 / (760 / 43) - 1 / (410 / 23)) +
    (-581 / 2) / 2 * (1 / (760 / 43) ^ 2 - 1 / (410 / 23) ^ 2)) = (303021066443711433353 / 7185174223458591360000)
  norm_num

private theorem inner_partial_sum_127 :
    (∑ i ∈ Finset.range 127, innerPieceValue i) = (81409371519421251563 / 1927729669708402560000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_126]
  change (303021066443711433353 / 7185174223458591360000) + ((167 / 10) * (1 / (410 / 23) - 1 / (660 / 37)) +
    -270 / 2 * (1 / (410 / 23) ^ 2 - 1 / (660 / 37) ^ 2)) = (81409371519421251563 / 1927729669708402560000)
  norm_num

private theorem inner_partial_sum_128 :
    (∑ i ∈ Finset.range 128, innerPieceValue i) = (2515340133869434411 / 58416050597224320000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_127]
  change (81409371519421251563 / 1927729669708402560000) + ((371 / 20) * (1 / (660 / 37) - 1 / 18) +
    -303 / 2 * (1 / (660 / 37) ^ 2 - 1 / 18 ^ 2)) = (2515340133869434411 / 58416050597224320000)
  norm_num

private theorem inner_partial_sum_129 :
    (∑ i ∈ Finset.range 129, innerPieceValue i) = (98035230807336150829 / 2278225973291748480000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_128]
  change (2515340133869434411 / 58416050597224320000) + ((177 / 10) * (1 / 18 - 1 / (780 / 43)) +
    -321 / 2 * (1 / 18 ^ 2 - 1 / (780 / 43) ^ 2)) = (98035230807336150829 / 2278225973291748480000)
  norm_num

private theorem inner_partial_sum_130 :
    (∑ i ∈ Finset.range 130, innerPieceValue i) = (52816347568143318631 / 1226737062541710720000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_129]
  change (98035230807336150829 / 2278225973291748480000) + ((177 / 10) * (1 / (780 / 43) - 1 / (420 / 23)) +
    -321 / 2 * (1 / (780 / 43) ^ 2 - 1 / (420 / 23) ^ 2)) = (52816347568143318631 / 1226737062541710720000)
  norm_num

private theorem inner_partial_sum_131 :
    (∑ i ∈ Finset.range 131, innerPieceValue i) = (128449727084362846961 / 2979218580458440320000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_130]
  change (52816347568143318631 / 1226737062541710720000) + ((331 / 20) * (1 / (420 / 23) - 1 / (680 / 37)) +
    -300 / 2 * (1 / (420 / 23) ^ 2 - 1 / (680 / 37) ^ 2)) = (128449727084362846961 / 2979218580458440320000)
  norm_num

private theorem inner_partial_sum_132 :
    (∑ i ∈ Finset.range 132, innerPieceValue i) = (280252059175511707021 / 6484181616291899520000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_131]
  change (128449727084362846961 / 2979218580458440320000) + ((847 / 40) * (1 / (680 / 37) - 1 / (37 / 2)) +
    -385 / 2 * (1 / (680 / 37) ^ 2 - 1 / (37 / 2) ^ 2)) = (280252059175511707021 / 6484181616291899520000)
  norm_num

private theorem inner_partial_sum_133 :
    (∑ i ∈ Finset.range 133, innerPieceValue i) = (30388217670048789739 / 700992607166691840000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_132]
  change (280252059175511707021 / 6484181616291899520000) + ((887 / 40) * (1 / (37 / 2) - 1 / (800 / 43)) +
    (-807 / 2) / 2 * (1 / (37 / 2) ^ 2 - 1 / (800 / 43) ^ 2)) = (30388217670048789739 / 700992607166691840000)
  norm_num

private theorem inner_partial_sum_134 :
    (∑ i ∈ Finset.range 134, innerPieceValue i) = (14092038464086667615347 / 324033832662803303040000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_133]
  change (30388217670048789739 / 700992607166691840000) + ((379 / 20) * (1 / (800 / 43) - 1 / (430 / 23)) +
    (-687 / 2) / 2 * (1 / (800 / 43) ^ 2 - 1 / (430 / 23) ^ 2)) = (14092038464086667615347 / 324033832662803303040000)
  norm_num

private theorem inner_partial_sum_135 :
    (∑ i ∈ Finset.range 135, innerPieceValue i) = (330948661396284592537 / 7535670527041937280000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_134]
  change (14092038464086667615347 / 324033832662803303040000) + ((89 / 5) * (1 / (430 / 23) - 1 / (700 / 37)) +
    -322 / 2 * (1 / (430 / 23) ^ 2 - 1 / (700 / 37) ^ 2)) = (330948661396284592537 / 7535670527041937280000)
  norm_num

private theorem inner_partial_sum_136 :
    (∑ i ∈ Finset.range 136, innerPieceValue i) = (6314515564686688895611 / 143177740013796808320000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_135]
  change (330948661396284592537 / 7535670527041937280000) + ((393 / 20) * (1 / (700 / 37) - 1 / 19) +
    -357 / 2 * (1 / (700 / 37) ^ 2 - 1 / 19 ^ 2)) = (6314515564686688895611 / 143177740013796808320000)
  norm_num

private theorem inner_partial_sum_137 :
    (∑ i ∈ Finset.range 137, innerPieceValue i) = (13569347630600699631329 / 308962491608719428480000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_136]
  change (6314515564686688895611 / 143177740013796808320000) + ((94 / 5) * (1 / 19 - 1 / (820 / 43)) +
    -376 / 2 * (1 / 19 ^ 2 - 1 / (820 / 43) ^ 2)) = (13569347630600699631329 / 308962491608719428480000)
  norm_num

private theorem inner_partial_sum_138 :
    (∑ i ∈ Finset.range 138, innerPieceValue i) = (3628346009801718502259 / 82892375797461310080000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_137]
  change (13569347630600699631329 / 308962491608719428480000) + ((94 / 5) * (1 / (820 / 43) - 1 / (440 / 23)) +
    -376 / 2 * (1 / (820 / 43) ^ 2 - 1 / (440 / 23) ^ 2)) = (3628346009801718502259 / 82892375797461310080000)
  norm_num

private theorem inner_partial_sum_139 :
    (∑ i ∈ Finset.range 139, innerPieceValue i) = (325200031085559118469 / 7535670527041937280000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_138]
  change (3628346009801718502259 / 82892375797461310080000) + ((353 / 20) * (1 / (440 / 23) - 1 / (720 / 37)) +
    -354 / 2 * (1 / (440 / 23) ^ 2 - 1 / (720 / 37) ^ 2)) = (325200031085559118469 / 7535670527041937280000)
  norm_num

private theorem inner_partial_sum_140 :
    (∑ i ∈ Finset.range 140, innerPieceValue i) = (4222179444545094496897 / 97963716851545184640000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_139]
  change (325200031085559118469 / 7535670527041937280000) + ((891 / 40) * (1 / (720 / 37) - 1 / (39 / 2)) +
    -444 / 2 * (1 / (720 / 37) ^ 2 - 1 / (39 / 2) ^ 2)) = (4222179444545094496897 / 97963716851545184640000)
  norm_num

private theorem inner_partial_sum_141 :
    (∑ i ∈ Finset.range 141, innerPieceValue i) = (2271196345609880684383 / 52749693689293560960000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_140]
  change (4222179444545094496897 / 97963716851545184640000) + ((931 / 40) * (1 / (39 / 2) - 1 / (840 / 43)) +
    (-927 / 2) / 2 * (1 / (39 / 2) ^ 2 - 1 / (840 / 43) ^ 2)) = (2271196345609880684383 / 52749693689293560960000)
  norm_num

private theorem inner_partial_sum_142 :
    (∑ i ∈ Finset.range 142, innerPieceValue i) = (324195926757243309661 / 7535670527041937280000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_141]
  change (2271196345609880684383 / 52749693689293560960000) + ((401 / 20) * (1 / (840 / 43) - 1 / (450 / 23)) +
    (-801 / 2) / 2 * (1 / (840 / 43) ^ 2 - 1 / (450 / 23) ^ 2)) = (324195926757243309661 / 7535670527041937280000)
  norm_num

private theorem inner_partial_sum_143 :
    (∑ i ∈ Finset.range 143, innerPieceValue i) = (322437603634266857629 / 7535670527041937280000) := by
  rw [Finset.sum_range_succ, inner_partial_sum_142]
  change (324195926757243309661 / 7535670527041937280000) + ((189 / 10) * (1 / (450 / 23) - 1 / 20) +
    -378 / 2 * (1 / (450 / 23) ^ 2 - 1 / 20 ^ 2)) = (322437603634266857629 / 7535670527041937280000)
  norm_num

theorem inner_exact_sum :
    (∑ i ∈ Finset.range 143, innerPieceValue i) = (322437603634266857629 / 7535670527041937280000) :=
  inner_partial_sum_143

end Zeta5.Certificate
