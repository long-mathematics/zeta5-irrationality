import Zeta5.Certificate.InnerBranches.Group14

/-! Generated source partition and branch assembly. -/

namespace Zeta5.Certificate

open Set

noncomputable def innerEndpoint : ℕ → ℝ
  | 0 => 3
  | 1 => (70 / 23)
  | 2 => (120 / 37)
  | 3 => (140 / 43)
  | 4 => (10 / 3)
  | 5 => (80 / 23)
  | 6 => (7 / 2)
  | 7 => (160 / 43)
  | 8 => (140 / 37)
  | 9 => (90 / 23)
  | 10 => 4
  | 11 => (180 / 43)
  | 12 => (160 / 37)
  | 13 => (100 / 23)
  | 14 => (9 / 2)
  | 15 => (200 / 43)
  | 16 => (110 / 23)
  | 17 => (180 / 37)
  | 18 => 5
  | 19 => (220 / 43)
  | 20 => (120 / 23)
  | 21 => (200 / 37)
  | 22 => (11 / 2)
  | 23 => (240 / 43)
  | 24 => (130 / 23)
  | 25 => (220 / 37)
  | 26 => 6
  | 27 => (260 / 43)
  | 28 => (140 / 23)
  | 29 => (240 / 37)
  | 30 => (13 / 2)
  | 31 => (280 / 43)
  | 32 => (150 / 23)
  | 33 => (20 / 3)
  | 34 => (160 / 23)
  | 35 => (300 / 43)
  | 36 => 7
  | 37 => (260 / 37)
  | 38 => (170 / 23)
  | 39 => (320 / 43)
  | 40 => (15 / 2)
  | 41 => (280 / 37)
  | 42 => (180 / 23)
  | 43 => (340 / 43)
  | 44 => 8
  | 45 => (300 / 37)
  | 46 => (190 / 23)
  | 47 => (360 / 43)
  | 48 => (17 / 2)
  | 49 => (320 / 37)
  | 50 => (200 / 23)
  | 51 => (380 / 43)
  | 52 => 9
  | 53 => (210 / 23)
  | 54 => (340 / 37)
  | 55 => (400 / 43)
  | 56 => (19 / 2)
  | 57 => (220 / 23)
  | 58 => (360 / 37)
  | 59 => (420 / 43)
  | 60 => 10
  | 61 => (440 / 43)
  | 62 => (380 / 37)
  | 63 => (240 / 23)
  | 64 => (21 / 2)
  | 65 => (460 / 43)
  | 66 => (400 / 37)
  | 67 => (250 / 23)
  | 68 => 11
  | 69 => (480 / 43)
  | 70 => (260 / 23)
  | 71 => (420 / 37)
  | 72 => (23 / 2)
  | 73 => (500 / 43)
  | 74 => (270 / 23)
  | 75 => (440 / 37)
  | 76 => 12
  | 77 => (520 / 43)
  | 78 => (280 / 23)
  | 79 => (460 / 37)
  | 80 => (25 / 2)
  | 81 => (540 / 43)
  | 82 => (290 / 23)
  | 83 => (480 / 37)
  | 84 => 13
  | 85 => (560 / 43)
  | 86 => (300 / 23)
  | 87 => (40 / 3)
  | 88 => (310 / 23)
  | 89 => (580 / 43)
  | 90 => (27 / 2)
  | 91 => (500 / 37)
  | 92 => (320 / 23)
  | 93 => (600 / 43)
  | 94 => 14
  | 95 => (520 / 37)
  | 96 => (330 / 23)
  | 97 => (620 / 43)
  | 98 => (29 / 2)
  | 99 => (540 / 37)
  | 100 => (340 / 23)
  | 101 => (640 / 43)
  | 102 => 15
  | 103 => (560 / 37)
  | 104 => (350 / 23)
  | 105 => (660 / 43)
  | 106 => (31 / 2)
  | 107 => (360 / 23)
  | 108 => (580 / 37)
  | 109 => (680 / 43)
  | 110 => 16
  | 111 => (370 / 23)
  | 112 => (600 / 37)
  | 113 => (700 / 43)
  | 114 => (33 / 2)
  | 115 => (380 / 23)
  | 116 => (50 / 3)
  | 117 => (720 / 43)
  | 118 => (620 / 37)
  | 119 => (390 / 23)
  | 120 => 17
  | 121 => (740 / 43)
  | 122 => (640 / 37)
  | 123 => (400 / 23)
  | 124 => (35 / 2)
  | 125 => (760 / 43)
  | 126 => (410 / 23)
  | 127 => (660 / 37)
  | 128 => 18
  | 129 => (780 / 43)
  | 130 => (420 / 23)
  | 131 => (680 / 37)
  | 132 => (37 / 2)
  | 133 => (800 / 43)
  | 134 => (430 / 23)
  | 135 => (700 / 37)
  | 136 => 19
  | 137 => (820 / 43)
  | 138 => (440 / 23)
  | 139 => (720 / 37)
  | 140 => (39 / 2)
  | 141 => (840 / 43)
  | 142 => (450 / 23)
  | 143 => 20
  | _ => 0

noncomputable def innerIntercept : ℕ → ℝ
  | 0 => -6
  | 1 => (-5 / 2)
  | 2 => (-35 / 2)
  | 3 => (-35 / 2)
  | 4 => -17
  | 5 => -13
  | 6 => (-33 / 2)
  | 7 => (-9 / 2)
  | 8 => (-23 / 2)
  | 9 => -7
  | 10 => -11
  | 11 => -11
  | 12 => -31
  | 13 => -26
  | 14 => (-61 / 2)
  | 15 => (-31 / 2)
  | 16 => -10
  | 17 => -19
  | 18 => -24
  | 19 => -24
  | 20 => -18
  | 21 => -43
  | 22 => (-97 / 2)
  | 23 => (-61 / 2)
  | 24 => -24
  | 25 => -35
  | 26 => -41
  | 27 => -41
  | 28 => -34
  | 29 => -64
  | 30 => (-141 / 2)
  | 31 => (-99 / 2)
  | 32 => -42
  | 33 => -50
  | 34 => -42
  | 35 => -42
  | 36 => -49
  | 37 => -62
  | 38 => (-107 / 2)
  | 39 => (-59 / 2)
  | 40 => -37
  | 41 => -72
  | 42 => -63
  | 43 => -63
  | 44 => -71
  | 45 => -86
  | 46 => (-153 / 2)
  | 47 => (-99 / 2)
  | 48 => -58
  | 49 => -98
  | 50 => -88
  | 51 => -88
  | 52 => -97
  | 53 => (-173 / 2)
  | 54 => (-207 / 2)
  | 55 => (-147 / 2)
  | 56 => -83
  | 57 => -72
  | 58 => -117
  | 59 => -117
  | 60 => -114
  | 61 => -81
  | 62 => -100
  | 63 => -88
  | 64 => (-197 / 2)
  | 65 => (-197 / 2)
  | 66 => (-297 / 2)
  | 67 => -136
  | 68 => -147
  | 69 => -111
  | 70 => -98
  | 71 => -119
  | 72 => (-261 / 2)
  | 73 => (-261 / 2)
  | 74 => -117
  | 75 => -172
  | 76 => -184
  | 77 => -145
  | 78 => -131
  | 79 => -154
  | 80 => (-333 / 2)
  | 81 => (-333 / 2)
  | 82 => -152
  | 83 => -212
  | 84 => -225
  | 85 => -183
  | 86 => -168
  | 87 => -184
  | 88 => (-337 / 2)
  | 89 => (-337 / 2)
  | 90 => -182
  | 91 => -207
  | 92 => -191
  | 93 => -146
  | 94 => -160
  | 95 => -225
  | 96 => (-417 / 2)
  | 97 => (-417 / 2)
  | 98 => -223
  | 99 => -250
  | 100 => -233
  | 101 => -185
  | 102 => -200
  | 103 => -270
  | 104 => (-505 / 2)
  | 105 => (-505 / 2)
  | 106 => -268
  | 107 => -250
  | 108 => -279
  | 109 => -228
  | 110 => -244
  | 111 => (-451 / 2)
  | 112 => (-601 / 2)
  | 113 => (-601 / 2)
  | 114 => -317
  | 115 => -298
  | 116 => (-591 / 2)
  | 117 => (-483 / 2)
  | 118 => (-545 / 2)
  | 119 => -253
  | 120 => -270
  | 121 => -270
  | 122 => -350
  | 123 => -330
  | 124 => (-695 / 2)
  | 125 => (-581 / 2)
  | 126 => -270
  | 127 => -303
  | 128 => -321
  | 129 => -321
  | 130 => -300
  | 131 => -385
  | 132 => (-807 / 2)
  | 133 => (-687 / 2)
  | 134 => -322
  | 135 => -357
  | 136 => -376
  | 137 => -376
  | 138 => -354
  | 139 => -444
  | 140 => (-927 / 2)
  | 141 => (-801 / 2)
  | 142 => -378
  | _ => 0

noncomputable def innerSlope : ℕ → ℝ
  | 0 => (18 / 5)
  | 1 => (49 / 20)
  | 2 => (283 / 40)
  | 3 => (283 / 40)
  | 4 => (277 / 40)
  | 5 => (231 / 40)
  | 6 => (271 / 40)
  | 7 => (71 / 20)
  | 8 => (27 / 5)
  | 9 => (17 / 4)
  | 10 => (17 / 5)
  | 11 => (17 / 5)
  | 12 => (321 / 40)
  | 13 => (55 / 8)
  | 14 => (63 / 8)
  | 15 => (93 / 20)
  | 16 => (7 / 2)
  | 17 => (107 / 20)
  | 18 => (9 / 2)
  | 19 => (9 / 2)
  | 20 => (67 / 20)
  | 21 => (319 / 40)
  | 22 => (359 / 40)
  | 23 => (23 / 4)
  | 24 => (23 / 5)
  | 25 => (129 / 20)
  | 26 => (28 / 5)
  | 27 => (28 / 5)
  | 28 => (89 / 20)
  | 29 => (363 / 40)
  | 30 => (403 / 40)
  | 31 => (137 / 20)
  | 32 => (57 / 10)
  | 33 => (69 / 10)
  | 34 => (23 / 4)
  | 35 => (23 / 4)
  | 36 => (49 / 10)
  | 37 => (27 / 4)
  | 38 => (28 / 5)
  | 39 => (19 / 8)
  | 40 => (27 / 8)
  | 41 => 8
  | 42 => (137 / 20)
  | 43 => (137 / 20)
  | 44 => 6
  | 45 => (157 / 20)
  | 46 => (67 / 10)
  | 47 => (139 / 40)
  | 48 => (179 / 40)
  | 49 => (91 / 10)
  | 50 => (159 / 20)
  | 51 => (159 / 20)
  | 52 => (71 / 10)
  | 53 => (119 / 20)
  | 54 => (39 / 5)
  | 55 => (183 / 40)
  | 56 => (223 / 40)
  | 57 => (177 / 40)
  | 58 => (181 / 20)
  | 59 => (181 / 20)
  | 60 => (69 / 10)
  | 61 => (147 / 40)
  | 62 => (221 / 40)
  | 63 => (35 / 8)
  | 64 => (43 / 8)
  | 65 => (43 / 8)
  | 66 => 10
  | 67 => (177 / 20)
  | 68 => 8
  | 69 => (191 / 40)
  | 70 => (29 / 8)
  | 71 => (219 / 40)
  | 72 => (259 / 40)
  | 73 => (259 / 40)
  | 74 => (213 / 40)
  | 75 => (199 / 20)
  | 76 => (91 / 10)
  | 77 => (47 / 8)
  | 78 => (189 / 40)
  | 79 => (263 / 40)
  | 80 => (303 / 40)
  | 81 => (303 / 40)
  | 82 => (257 / 40)
  | 83 => (221 / 20)
  | 84 => (51 / 5)
  | 85 => (279 / 40)
  | 86 => (233 / 40)
  | 87 => (145 / 8)
  | 88 => (679 / 40)
  | 89 => (679 / 40)
  | 90 => (719 / 40)
  | 91 => (793 / 40)
  | 92 => (747 / 40)
  | 93 => (309 / 20)
  | 94 => (73 / 5)
  | 95 => (769 / 40)
  | 96 => (723 / 40)
  | 97 => (723 / 40)
  | 98 => (763 / 40)
  | 99 => (837 / 40)
  | 100 => (791 / 40)
  | 101 => (331 / 20)
  | 102 => (157 / 10)
  | 103 => (813 / 40)
  | 104 => (767 / 40)
  | 105 => (767 / 40)
  | 106 => (807 / 40)
  | 107 => (761 / 40)
  | 108 => (167 / 8)
  | 109 => (353 / 20)
  | 110 => (84 / 5)
  | 111 => (313 / 20)
  | 112 => (811 / 40)
  | 113 => (811 / 40)
  | 114 => (851 / 40)
  | 115 => (161 / 8)
  | 116 => (799 / 40)
  | 117 => (67 / 4)
  | 118 => (93 / 5)
  | 119 => (349 / 20)
  | 120 => (83 / 5)
  | 121 => (83 / 5)
  | 122 => (849 / 40)
  | 123 => (803 / 40)
  | 124 => (843 / 40)
  | 125 => (357 / 20)
  | 126 => (167 / 10)
  | 127 => (371 / 20)
  | 128 => (177 / 10)
  | 129 => (177 / 10)
  | 130 => (331 / 20)
  | 131 => (847 / 40)
  | 132 => (887 / 40)
  | 133 => (379 / 20)
  | 134 => (89 / 5)
  | 135 => (393 / 20)
  | 136 => (94 / 5)
  | 137 => (94 / 5)
  | 138 => (353 / 20)
  | 139 => (891 / 40)
  | 140 => (931 / 40)
  | 141 => (401 / 20)
  | 142 => (189 / 10)
  | _ => 0

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

theorem innerEndpoint_increasing (i : ℕ) (hi : i < 143) :
    innerEndpoint i < innerEndpoint (i + 1) := by
  interval_cases i
  · change (3 : ℝ) < (70 / 23)
    norm_num
  · change ((70 / 23) : ℝ) < (120 / 37)
    norm_num
  · change ((120 / 37) : ℝ) < (140 / 43)
    norm_num
  · change ((140 / 43) : ℝ) < (10 / 3)
    norm_num
  · change ((10 / 3) : ℝ) < (80 / 23)
    norm_num
  · change ((80 / 23) : ℝ) < (7 / 2)
    norm_num
  · change ((7 / 2) : ℝ) < (160 / 43)
    norm_num
  · change ((160 / 43) : ℝ) < (140 / 37)
    norm_num
  · change ((140 / 37) : ℝ) < (90 / 23)
    norm_num
  · change ((90 / 23) : ℝ) < 4
    norm_num
  · change (4 : ℝ) < (180 / 43)
    norm_num
  · change ((180 / 43) : ℝ) < (160 / 37)
    norm_num
  · change ((160 / 37) : ℝ) < (100 / 23)
    norm_num
  · change ((100 / 23) : ℝ) < (9 / 2)
    norm_num
  · change ((9 / 2) : ℝ) < (200 / 43)
    norm_num
  · change ((200 / 43) : ℝ) < (110 / 23)
    norm_num
  · change ((110 / 23) : ℝ) < (180 / 37)
    norm_num
  · change ((180 / 37) : ℝ) < 5
    norm_num
  · change (5 : ℝ) < (220 / 43)
    norm_num
  · change ((220 / 43) : ℝ) < (120 / 23)
    norm_num
  · change ((120 / 23) : ℝ) < (200 / 37)
    norm_num
  · change ((200 / 37) : ℝ) < (11 / 2)
    norm_num
  · change ((11 / 2) : ℝ) < (240 / 43)
    norm_num
  · change ((240 / 43) : ℝ) < (130 / 23)
    norm_num
  · change ((130 / 23) : ℝ) < (220 / 37)
    norm_num
  · change ((220 / 37) : ℝ) < 6
    norm_num
  · change (6 : ℝ) < (260 / 43)
    norm_num
  · change ((260 / 43) : ℝ) < (140 / 23)
    norm_num
  · change ((140 / 23) : ℝ) < (240 / 37)
    norm_num
  · change ((240 / 37) : ℝ) < (13 / 2)
    norm_num
  · change ((13 / 2) : ℝ) < (280 / 43)
    norm_num
  · change ((280 / 43) : ℝ) < (150 / 23)
    norm_num
  · change ((150 / 23) : ℝ) < (20 / 3)
    norm_num
  · change ((20 / 3) : ℝ) < (160 / 23)
    norm_num
  · change ((160 / 23) : ℝ) < (300 / 43)
    norm_num
  · change ((300 / 43) : ℝ) < 7
    norm_num
  · change (7 : ℝ) < (260 / 37)
    norm_num
  · change ((260 / 37) : ℝ) < (170 / 23)
    norm_num
  · change ((170 / 23) : ℝ) < (320 / 43)
    norm_num
  · change ((320 / 43) : ℝ) < (15 / 2)
    norm_num
  · change ((15 / 2) : ℝ) < (280 / 37)
    norm_num
  · change ((280 / 37) : ℝ) < (180 / 23)
    norm_num
  · change ((180 / 23) : ℝ) < (340 / 43)
    norm_num
  · change ((340 / 43) : ℝ) < 8
    norm_num
  · change (8 : ℝ) < (300 / 37)
    norm_num
  · change ((300 / 37) : ℝ) < (190 / 23)
    norm_num
  · change ((190 / 23) : ℝ) < (360 / 43)
    norm_num
  · change ((360 / 43) : ℝ) < (17 / 2)
    norm_num
  · change ((17 / 2) : ℝ) < (320 / 37)
    norm_num
  · change ((320 / 37) : ℝ) < (200 / 23)
    norm_num
  · change ((200 / 23) : ℝ) < (380 / 43)
    norm_num
  · change ((380 / 43) : ℝ) < 9
    norm_num
  · change (9 : ℝ) < (210 / 23)
    norm_num
  · change ((210 / 23) : ℝ) < (340 / 37)
    norm_num
  · change ((340 / 37) : ℝ) < (400 / 43)
    norm_num
  · change ((400 / 43) : ℝ) < (19 / 2)
    norm_num
  · change ((19 / 2) : ℝ) < (220 / 23)
    norm_num
  · change ((220 / 23) : ℝ) < (360 / 37)
    norm_num
  · change ((360 / 37) : ℝ) < (420 / 43)
    norm_num
  · change ((420 / 43) : ℝ) < 10
    norm_num
  · change (10 : ℝ) < (440 / 43)
    norm_num
  · change ((440 / 43) : ℝ) < (380 / 37)
    norm_num
  · change ((380 / 37) : ℝ) < (240 / 23)
    norm_num
  · change ((240 / 23) : ℝ) < (21 / 2)
    norm_num
  · change ((21 / 2) : ℝ) < (460 / 43)
    norm_num
  · change ((460 / 43) : ℝ) < (400 / 37)
    norm_num
  · change ((400 / 37) : ℝ) < (250 / 23)
    norm_num
  · change ((250 / 23) : ℝ) < 11
    norm_num
  · change (11 : ℝ) < (480 / 43)
    norm_num
  · change ((480 / 43) : ℝ) < (260 / 23)
    norm_num
  · change ((260 / 23) : ℝ) < (420 / 37)
    norm_num
  · change ((420 / 37) : ℝ) < (23 / 2)
    norm_num
  · change ((23 / 2) : ℝ) < (500 / 43)
    norm_num
  · change ((500 / 43) : ℝ) < (270 / 23)
    norm_num
  · change ((270 / 23) : ℝ) < (440 / 37)
    norm_num
  · change ((440 / 37) : ℝ) < 12
    norm_num
  · change (12 : ℝ) < (520 / 43)
    norm_num
  · change ((520 / 43) : ℝ) < (280 / 23)
    norm_num
  · change ((280 / 23) : ℝ) < (460 / 37)
    norm_num
  · change ((460 / 37) : ℝ) < (25 / 2)
    norm_num
  · change ((25 / 2) : ℝ) < (540 / 43)
    norm_num
  · change ((540 / 43) : ℝ) < (290 / 23)
    norm_num
  · change ((290 / 23) : ℝ) < (480 / 37)
    norm_num
  · change ((480 / 37) : ℝ) < 13
    norm_num
  · change (13 : ℝ) < (560 / 43)
    norm_num
  · change ((560 / 43) : ℝ) < (300 / 23)
    norm_num
  · change ((300 / 23) : ℝ) < (40 / 3)
    norm_num
  · change ((40 / 3) : ℝ) < (310 / 23)
    norm_num
  · change ((310 / 23) : ℝ) < (580 / 43)
    norm_num
  · change ((580 / 43) : ℝ) < (27 / 2)
    norm_num
  · change ((27 / 2) : ℝ) < (500 / 37)
    norm_num
  · change ((500 / 37) : ℝ) < (320 / 23)
    norm_num
  · change ((320 / 23) : ℝ) < (600 / 43)
    norm_num
  · change ((600 / 43) : ℝ) < 14
    norm_num
  · change (14 : ℝ) < (520 / 37)
    norm_num
  · change ((520 / 37) : ℝ) < (330 / 23)
    norm_num
  · change ((330 / 23) : ℝ) < (620 / 43)
    norm_num
  · change ((620 / 43) : ℝ) < (29 / 2)
    norm_num
  · change ((29 / 2) : ℝ) < (540 / 37)
    norm_num
  · change ((540 / 37) : ℝ) < (340 / 23)
    norm_num
  · change ((340 / 23) : ℝ) < (640 / 43)
    norm_num
  · change ((640 / 43) : ℝ) < 15
    norm_num
  · change (15 : ℝ) < (560 / 37)
    norm_num
  · change ((560 / 37) : ℝ) < (350 / 23)
    norm_num
  · change ((350 / 23) : ℝ) < (660 / 43)
    norm_num
  · change ((660 / 43) : ℝ) < (31 / 2)
    norm_num
  · change ((31 / 2) : ℝ) < (360 / 23)
    norm_num
  · change ((360 / 23) : ℝ) < (580 / 37)
    norm_num
  · change ((580 / 37) : ℝ) < (680 / 43)
    norm_num
  · change ((680 / 43) : ℝ) < 16
    norm_num
  · change (16 : ℝ) < (370 / 23)
    norm_num
  · change ((370 / 23) : ℝ) < (600 / 37)
    norm_num
  · change ((600 / 37) : ℝ) < (700 / 43)
    norm_num
  · change ((700 / 43) : ℝ) < (33 / 2)
    norm_num
  · change ((33 / 2) : ℝ) < (380 / 23)
    norm_num
  · change ((380 / 23) : ℝ) < (50 / 3)
    norm_num
  · change ((50 / 3) : ℝ) < (720 / 43)
    norm_num
  · change ((720 / 43) : ℝ) < (620 / 37)
    norm_num
  · change ((620 / 37) : ℝ) < (390 / 23)
    norm_num
  · change ((390 / 23) : ℝ) < 17
    norm_num
  · change (17 : ℝ) < (740 / 43)
    norm_num
  · change ((740 / 43) : ℝ) < (640 / 37)
    norm_num
  · change ((640 / 37) : ℝ) < (400 / 23)
    norm_num
  · change ((400 / 23) : ℝ) < (35 / 2)
    norm_num
  · change ((35 / 2) : ℝ) < (760 / 43)
    norm_num
  · change ((760 / 43) : ℝ) < (410 / 23)
    norm_num
  · change ((410 / 23) : ℝ) < (660 / 37)
    norm_num
  · change ((660 / 37) : ℝ) < 18
    norm_num
  · change (18 : ℝ) < (780 / 43)
    norm_num
  · change ((780 / 43) : ℝ) < (420 / 23)
    norm_num
  · change ((420 / 23) : ℝ) < (680 / 37)
    norm_num
  · change ((680 / 37) : ℝ) < (37 / 2)
    norm_num
  · change ((37 / 2) : ℝ) < (800 / 43)
    norm_num
  · change ((800 / 43) : ℝ) < (430 / 23)
    norm_num
  · change ((430 / 23) : ℝ) < (700 / 37)
    norm_num
  · change ((700 / 37) : ℝ) < 19
    norm_num
  · change (19 : ℝ) < (820 / 43)
    norm_num
  · change ((820 / 43) : ℝ) < (440 / 23)
    norm_num
  · change ((440 / 23) : ℝ) < (720 / 37)
    norm_num
  · change ((720 / 37) : ℝ) < (39 / 2)
    norm_num
  · change ((39 / 2) : ℝ) < (840 / 43)
    norm_num
  · change ((840 / 43) : ℝ) < (450 / 23)
    norm_num
  · change ((450 / 23) : ℝ) < 20
    norm_num

theorem innerEndpoint_pos (i : ℕ) (hi : i ≤ 143) :
    0 < innerEndpoint i := by
  interval_cases i
  · change (0 : ℝ) < 3
    norm_num
  · change (0 : ℝ) < (70 / 23)
    norm_num
  · change (0 : ℝ) < (120 / 37)
    norm_num
  · change (0 : ℝ) < (140 / 43)
    norm_num
  · change (0 : ℝ) < (10 / 3)
    norm_num
  · change (0 : ℝ) < (80 / 23)
    norm_num
  · change (0 : ℝ) < (7 / 2)
    norm_num
  · change (0 : ℝ) < (160 / 43)
    norm_num
  · change (0 : ℝ) < (140 / 37)
    norm_num
  · change (0 : ℝ) < (90 / 23)
    norm_num
  · change (0 : ℝ) < 4
    norm_num
  · change (0 : ℝ) < (180 / 43)
    norm_num
  · change (0 : ℝ) < (160 / 37)
    norm_num
  · change (0 : ℝ) < (100 / 23)
    norm_num
  · change (0 : ℝ) < (9 / 2)
    norm_num
  · change (0 : ℝ) < (200 / 43)
    norm_num
  · change (0 : ℝ) < (110 / 23)
    norm_num
  · change (0 : ℝ) < (180 / 37)
    norm_num
  · change (0 : ℝ) < 5
    norm_num
  · change (0 : ℝ) < (220 / 43)
    norm_num
  · change (0 : ℝ) < (120 / 23)
    norm_num
  · change (0 : ℝ) < (200 / 37)
    norm_num
  · change (0 : ℝ) < (11 / 2)
    norm_num
  · change (0 : ℝ) < (240 / 43)
    norm_num
  · change (0 : ℝ) < (130 / 23)
    norm_num
  · change (0 : ℝ) < (220 / 37)
    norm_num
  · change (0 : ℝ) < 6
    norm_num
  · change (0 : ℝ) < (260 / 43)
    norm_num
  · change (0 : ℝ) < (140 / 23)
    norm_num
  · change (0 : ℝ) < (240 / 37)
    norm_num
  · change (0 : ℝ) < (13 / 2)
    norm_num
  · change (0 : ℝ) < (280 / 43)
    norm_num
  · change (0 : ℝ) < (150 / 23)
    norm_num
  · change (0 : ℝ) < (20 / 3)
    norm_num
  · change (0 : ℝ) < (160 / 23)
    norm_num
  · change (0 : ℝ) < (300 / 43)
    norm_num
  · change (0 : ℝ) < 7
    norm_num
  · change (0 : ℝ) < (260 / 37)
    norm_num
  · change (0 : ℝ) < (170 / 23)
    norm_num
  · change (0 : ℝ) < (320 / 43)
    norm_num
  · change (0 : ℝ) < (15 / 2)
    norm_num
  · change (0 : ℝ) < (280 / 37)
    norm_num
  · change (0 : ℝ) < (180 / 23)
    norm_num
  · change (0 : ℝ) < (340 / 43)
    norm_num
  · change (0 : ℝ) < 8
    norm_num
  · change (0 : ℝ) < (300 / 37)
    norm_num
  · change (0 : ℝ) < (190 / 23)
    norm_num
  · change (0 : ℝ) < (360 / 43)
    norm_num
  · change (0 : ℝ) < (17 / 2)
    norm_num
  · change (0 : ℝ) < (320 / 37)
    norm_num
  · change (0 : ℝ) < (200 / 23)
    norm_num
  · change (0 : ℝ) < (380 / 43)
    norm_num
  · change (0 : ℝ) < 9
    norm_num
  · change (0 : ℝ) < (210 / 23)
    norm_num
  · change (0 : ℝ) < (340 / 37)
    norm_num
  · change (0 : ℝ) < (400 / 43)
    norm_num
  · change (0 : ℝ) < (19 / 2)
    norm_num
  · change (0 : ℝ) < (220 / 23)
    norm_num
  · change (0 : ℝ) < (360 / 37)
    norm_num
  · change (0 : ℝ) < (420 / 43)
    norm_num
  · change (0 : ℝ) < 10
    norm_num
  · change (0 : ℝ) < (440 / 43)
    norm_num
  · change (0 : ℝ) < (380 / 37)
    norm_num
  · change (0 : ℝ) < (240 / 23)
    norm_num
  · change (0 : ℝ) < (21 / 2)
    norm_num
  · change (0 : ℝ) < (460 / 43)
    norm_num
  · change (0 : ℝ) < (400 / 37)
    norm_num
  · change (0 : ℝ) < (250 / 23)
    norm_num
  · change (0 : ℝ) < 11
    norm_num
  · change (0 : ℝ) < (480 / 43)
    norm_num
  · change (0 : ℝ) < (260 / 23)
    norm_num
  · change (0 : ℝ) < (420 / 37)
    norm_num
  · change (0 : ℝ) < (23 / 2)
    norm_num
  · change (0 : ℝ) < (500 / 43)
    norm_num
  · change (0 : ℝ) < (270 / 23)
    norm_num
  · change (0 : ℝ) < (440 / 37)
    norm_num
  · change (0 : ℝ) < 12
    norm_num
  · change (0 : ℝ) < (520 / 43)
    norm_num
  · change (0 : ℝ) < (280 / 23)
    norm_num
  · change (0 : ℝ) < (460 / 37)
    norm_num
  · change (0 : ℝ) < (25 / 2)
    norm_num
  · change (0 : ℝ) < (540 / 43)
    norm_num
  · change (0 : ℝ) < (290 / 23)
    norm_num
  · change (0 : ℝ) < (480 / 37)
    norm_num
  · change (0 : ℝ) < 13
    norm_num
  · change (0 : ℝ) < (560 / 43)
    norm_num
  · change (0 : ℝ) < (300 / 23)
    norm_num
  · change (0 : ℝ) < (40 / 3)
    norm_num
  · change (0 : ℝ) < (310 / 23)
    norm_num
  · change (0 : ℝ) < (580 / 43)
    norm_num
  · change (0 : ℝ) < (27 / 2)
    norm_num
  · change (0 : ℝ) < (500 / 37)
    norm_num
  · change (0 : ℝ) < (320 / 23)
    norm_num
  · change (0 : ℝ) < (600 / 43)
    norm_num
  · change (0 : ℝ) < 14
    norm_num
  · change (0 : ℝ) < (520 / 37)
    norm_num
  · change (0 : ℝ) < (330 / 23)
    norm_num
  · change (0 : ℝ) < (620 / 43)
    norm_num
  · change (0 : ℝ) < (29 / 2)
    norm_num
  · change (0 : ℝ) < (540 / 37)
    norm_num
  · change (0 : ℝ) < (340 / 23)
    norm_num
  · change (0 : ℝ) < (640 / 43)
    norm_num
  · change (0 : ℝ) < 15
    norm_num
  · change (0 : ℝ) < (560 / 37)
    norm_num
  · change (0 : ℝ) < (350 / 23)
    norm_num
  · change (0 : ℝ) < (660 / 43)
    norm_num
  · change (0 : ℝ) < (31 / 2)
    norm_num
  · change (0 : ℝ) < (360 / 23)
    norm_num
  · change (0 : ℝ) < (580 / 37)
    norm_num
  · change (0 : ℝ) < (680 / 43)
    norm_num
  · change (0 : ℝ) < 16
    norm_num
  · change (0 : ℝ) < (370 / 23)
    norm_num
  · change (0 : ℝ) < (600 / 37)
    norm_num
  · change (0 : ℝ) < (700 / 43)
    norm_num
  · change (0 : ℝ) < (33 / 2)
    norm_num
  · change (0 : ℝ) < (380 / 23)
    norm_num
  · change (0 : ℝ) < (50 / 3)
    norm_num
  · change (0 : ℝ) < (720 / 43)
    norm_num
  · change (0 : ℝ) < (620 / 37)
    norm_num
  · change (0 : ℝ) < (390 / 23)
    norm_num
  · change (0 : ℝ) < 17
    norm_num
  · change (0 : ℝ) < (740 / 43)
    norm_num
  · change (0 : ℝ) < (640 / 37)
    norm_num
  · change (0 : ℝ) < (400 / 23)
    norm_num
  · change (0 : ℝ) < (35 / 2)
    norm_num
  · change (0 : ℝ) < (760 / 43)
    norm_num
  · change (0 : ℝ) < (410 / 23)
    norm_num
  · change (0 : ℝ) < (660 / 37)
    norm_num
  · change (0 : ℝ) < 18
    norm_num
  · change (0 : ℝ) < (780 / 43)
    norm_num
  · change (0 : ℝ) < (420 / 23)
    norm_num
  · change (0 : ℝ) < (680 / 37)
    norm_num
  · change (0 : ℝ) < (37 / 2)
    norm_num
  · change (0 : ℝ) < (800 / 43)
    norm_num
  · change (0 : ℝ) < (430 / 23)
    norm_num
  · change (0 : ℝ) < (700 / 37)
    norm_num
  · change (0 : ℝ) < 19
    norm_num
  · change (0 : ℝ) < (820 / 43)
    norm_num
  · change (0 : ℝ) < (440 / 23)
    norm_num
  · change (0 : ℝ) < (720 / 37)
    norm_num
  · change (0 : ℝ) < (39 / 2)
    norm_num
  · change (0 : ℝ) < (840 / 43)
    norm_num
  · change (0 : ℝ) < (450 / 23)
    norm_num
  · change (0 : ℝ) < 20
    norm_num

theorem inner_branches (i : ℕ) (hi : i < 143) (x : ℝ)
    (hx : x ∈ Ioo (innerEndpoint i) (innerEndpoint (i + 1))) :
    innerR x = innerIntercept i + innerSlope i * x := by
  interval_cases i
  · exact inner_branch_0 x hx.1 hx.2
  · exact inner_branch_1 x hx.1 hx.2
  · exact inner_branch_2 x hx.1 hx.2
  · exact inner_branch_3 x hx.1 hx.2
  · exact inner_branch_4 x hx.1 hx.2
  · exact inner_branch_5 x hx.1 hx.2
  · exact inner_branch_6 x hx.1 hx.2
  · exact inner_branch_7 x hx.1 hx.2
  · exact inner_branch_8 x hx.1 hx.2
  · exact inner_branch_9 x hx.1 hx.2
  · exact inner_branch_10 x hx.1 hx.2
  · exact inner_branch_11 x hx.1 hx.2
  · exact inner_branch_12 x hx.1 hx.2
  · exact inner_branch_13 x hx.1 hx.2
  · exact inner_branch_14 x hx.1 hx.2
  · exact inner_branch_15 x hx.1 hx.2
  · exact inner_branch_16 x hx.1 hx.2
  · exact inner_branch_17 x hx.1 hx.2
  · exact inner_branch_18 x hx.1 hx.2
  · exact inner_branch_19 x hx.1 hx.2
  · exact inner_branch_20 x hx.1 hx.2
  · exact inner_branch_21 x hx.1 hx.2
  · exact inner_branch_22 x hx.1 hx.2
  · exact inner_branch_23 x hx.1 hx.2
  · exact inner_branch_24 x hx.1 hx.2
  · exact inner_branch_25 x hx.1 hx.2
  · exact inner_branch_26 x hx.1 hx.2
  · exact inner_branch_27 x hx.1 hx.2
  · exact inner_branch_28 x hx.1 hx.2
  · exact inner_branch_29 x hx.1 hx.2
  · exact inner_branch_30 x hx.1 hx.2
  · exact inner_branch_31 x hx.1 hx.2
  · exact inner_branch_32 x hx.1 hx.2
  · exact inner_branch_33 x hx.1 hx.2
  · exact inner_branch_34 x hx.1 hx.2
  · exact inner_branch_35 x hx.1 hx.2
  · exact inner_branch_36 x hx.1 hx.2
  · exact inner_branch_37 x hx.1 hx.2
  · exact inner_branch_38 x hx.1 hx.2
  · exact inner_branch_39 x hx.1 hx.2
  · exact inner_branch_40 x hx.1 hx.2
  · exact inner_branch_41 x hx.1 hx.2
  · exact inner_branch_42 x hx.1 hx.2
  · exact inner_branch_43 x hx.1 hx.2
  · exact inner_branch_44 x hx.1 hx.2
  · exact inner_branch_45 x hx.1 hx.2
  · exact inner_branch_46 x hx.1 hx.2
  · exact inner_branch_47 x hx.1 hx.2
  · exact inner_branch_48 x hx.1 hx.2
  · exact inner_branch_49 x hx.1 hx.2
  · exact inner_branch_50 x hx.1 hx.2
  · exact inner_branch_51 x hx.1 hx.2
  · exact inner_branch_52 x hx.1 hx.2
  · exact inner_branch_53 x hx.1 hx.2
  · exact inner_branch_54 x hx.1 hx.2
  · exact inner_branch_55 x hx.1 hx.2
  · exact inner_branch_56 x hx.1 hx.2
  · exact inner_branch_57 x hx.1 hx.2
  · exact inner_branch_58 x hx.1 hx.2
  · exact inner_branch_59 x hx.1 hx.2
  · exact inner_branch_60 x hx.1 hx.2
  · exact inner_branch_61 x hx.1 hx.2
  · exact inner_branch_62 x hx.1 hx.2
  · exact inner_branch_63 x hx.1 hx.2
  · exact inner_branch_64 x hx.1 hx.2
  · exact inner_branch_65 x hx.1 hx.2
  · exact inner_branch_66 x hx.1 hx.2
  · exact inner_branch_67 x hx.1 hx.2
  · exact inner_branch_68 x hx.1 hx.2
  · exact inner_branch_69 x hx.1 hx.2
  · exact inner_branch_70 x hx.1 hx.2
  · exact inner_branch_71 x hx.1 hx.2
  · exact inner_branch_72 x hx.1 hx.2
  · exact inner_branch_73 x hx.1 hx.2
  · exact inner_branch_74 x hx.1 hx.2
  · exact inner_branch_75 x hx.1 hx.2
  · exact inner_branch_76 x hx.1 hx.2
  · exact inner_branch_77 x hx.1 hx.2
  · exact inner_branch_78 x hx.1 hx.2
  · exact inner_branch_79 x hx.1 hx.2
  · exact inner_branch_80 x hx.1 hx.2
  · exact inner_branch_81 x hx.1 hx.2
  · exact inner_branch_82 x hx.1 hx.2
  · exact inner_branch_83 x hx.1 hx.2
  · exact inner_branch_84 x hx.1 hx.2
  · exact inner_branch_85 x hx.1 hx.2
  · exact inner_branch_86 x hx.1 hx.2
  · exact inner_branch_87 x hx.1 hx.2
  · exact inner_branch_88 x hx.1 hx.2
  · exact inner_branch_89 x hx.1 hx.2
  · exact inner_branch_90 x hx.1 hx.2
  · exact inner_branch_91 x hx.1 hx.2
  · exact inner_branch_92 x hx.1 hx.2
  · exact inner_branch_93 x hx.1 hx.2
  · exact inner_branch_94 x hx.1 hx.2
  · exact inner_branch_95 x hx.1 hx.2
  · exact inner_branch_96 x hx.1 hx.2
  · exact inner_branch_97 x hx.1 hx.2
  · exact inner_branch_98 x hx.1 hx.2
  · exact inner_branch_99 x hx.1 hx.2
  · exact inner_branch_100 x hx.1 hx.2
  · exact inner_branch_101 x hx.1 hx.2
  · exact inner_branch_102 x hx.1 hx.2
  · exact inner_branch_103 x hx.1 hx.2
  · exact inner_branch_104 x hx.1 hx.2
  · exact inner_branch_105 x hx.1 hx.2
  · exact inner_branch_106 x hx.1 hx.2
  · exact inner_branch_107 x hx.1 hx.2
  · exact inner_branch_108 x hx.1 hx.2
  · exact inner_branch_109 x hx.1 hx.2
  · exact inner_branch_110 x hx.1 hx.2
  · exact inner_branch_111 x hx.1 hx.2
  · exact inner_branch_112 x hx.1 hx.2
  · exact inner_branch_113 x hx.1 hx.2
  · exact inner_branch_114 x hx.1 hx.2
  · exact inner_branch_115 x hx.1 hx.2
  · exact inner_branch_116 x hx.1 hx.2
  · exact inner_branch_117 x hx.1 hx.2
  · exact inner_branch_118 x hx.1 hx.2
  · exact inner_branch_119 x hx.1 hx.2
  · exact inner_branch_120 x hx.1 hx.2
  · exact inner_branch_121 x hx.1 hx.2
  · exact inner_branch_122 x hx.1 hx.2
  · exact inner_branch_123 x hx.1 hx.2
  · exact inner_branch_124 x hx.1 hx.2
  · exact inner_branch_125 x hx.1 hx.2
  · exact inner_branch_126 x hx.1 hx.2
  · exact inner_branch_127 x hx.1 hx.2
  · exact inner_branch_128 x hx.1 hx.2
  · exact inner_branch_129 x hx.1 hx.2
  · exact inner_branch_130 x hx.1 hx.2
  · exact inner_branch_131 x hx.1 hx.2
  · exact inner_branch_132 x hx.1 hx.2
  · exact inner_branch_133 x hx.1 hx.2
  · exact inner_branch_134 x hx.1 hx.2
  · exact inner_branch_135 x hx.1 hx.2
  · exact inner_branch_136 x hx.1 hx.2
  · exact inner_branch_137 x hx.1 hx.2
  · exact inner_branch_138 x hx.1 hx.2
  · exact inner_branch_139 x hx.1 hx.2
  · exact inner_branch_140 x hx.1 hx.2
  · exact inner_branch_141 x hx.1 hx.2
  · exact inner_branch_142 x hx.1 hx.2

end Zeta5.Certificate
