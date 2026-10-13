/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigRectangleEnergy

namespace Li2Lean.P0.ConfigRectangleBounds
open Li2Lean.P0.CA.Pinned Li2Lean.P0.ConfigSegment
open Li2Lean.P0.ConfigQLogSegments Li2Lean.P0.ConfigQLogDecomposition
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

def rowI (n : ℕ) (u v : List ℕ) (r : ℕ → ℕ → QI) (i : ℕ) : QI :=
  sumIdx n (fun j => QI.smul (densityQ u i * densityQ v j) (r i j))

def rowsI (m : ℕ) (tab : List QI) : QI := sumIdx m (fun i => tab.getD i (QI.pt 0))

theorem checkedRows_sound (m n : ℕ) (u v : List ℕ) (r : ℕ → ℕ → QI)
    (f : ℕ → ℕ → ℝ) (tab : List QI)
    (hc : ∀ i < m, QI.subset (rowI n u v r i) (tab.getD i (QI.pt 0)) = true)
    (hr : ∀ i < m, ∀ j < n, (r i j).Contains (f i j)) :
    (rowsI m tab).Contains (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n,
      referenceDensity u i * referenceDensity v j * f i j) := by
  apply sumIdx_sound
  intro i hi
  apply QI.mem_of_subset (hc i hi)
  apply sumIdx_sound
  intro j hj
  simpa only [Rat.cast_mul, densityQ_cast] using
    QI.mem_smul (densityQ u i * densityQ v j) (hr i hi j hj)

def pinnedRows : List QI := [
  ⟨-1/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨-2114720085/1000000000000, -2114717116/1000000000000⟩,
  ⟨-8085102070/1000000000000, -8085092060/1000000000000⟩,
  ⟨-11102845343/1000000000000, -11102832941/1000000000000⟩,
  ⟨-14038531257/1000000000000, -14038516870/1000000000000⟩,
  ⟨-16680137859/1000000000000, -16680121979/1000000000000⟩,
  ⟨-19156297866/1000000000000, -19156280754/1000000000000⟩,
  ⟨-21492189799/1000000000000, -21492171640/1000000000000⟩,
  ⟨-23711431302/1000000000000, -23711412222/1000000000000⟩,
  ⟨-25831025330/1000000000000, -25831005420/1000000000000⟩,
  ⟨-27865434891/1000000000000, -27865414215/1000000000000⟩,
  ⟨-29830610217/1000000000000, -29830588815/1000000000000⟩,
  ⟨-31744764248/1000000000000, -31744742139/1000000000000⟩,
  ⟨-33633865318/1000000000000, -33633842498/1000000000000⟩,
  ⟨-35531083656/1000000000000, -35531060095/1000000000000⟩,
  ⟨-37546002083/1000000000000, -37545977678/1000000000000⟩,
  ⟨-39593608838/1000000000000, -39593583543/1000000000000⟩,
  ⟨-44034181394/1000000000000, -44034153671/1000000000000⟩,
  ⟨-44328626304/1000000000000, -44328598590/1000000000000⟩,
  ⟨-44379173585/1000000000000, -44379145871/1000000000000⟩,
  ⟨-44221611555/1000000000000, -44221583841/1000000000000⟩,
  ⟨-43865373006/1000000000000, -43865345292/1000000000000⟩,
  ⟨-43310387439/1000000000000, -43310359725/1000000000000⟩,
  ⟨-42549841331/1000000000000, -42549813617/1000000000000⟩,
  ⟨-41570061316/1000000000000, -41570033601/1000000000000⟩,
  ⟨-40348498520/1000000000000, -40348470806/1000000000000⟩,
  ⟨-38848871709/1000000000000, -38848843995/1000000000000⟩,
  ⟨-37009692359/1000000000000, -37009664645/1000000000000⟩,
  ⟨-34711074175/1000000000000, -34711046461/1000000000000⟩,
  ⟨-31597557243/1000000000000, -31597529429/1000000000000⟩
]

theorem pinnedRow0 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 0) (pinnedRows.getD 0 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow1 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 1) (pinnedRows.getD 1 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow2 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 2) (pinnedRows.getD 2 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow3 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 3) (pinnedRows.getD 3 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow4 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 4) (pinnedRows.getD 4 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow5 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 5) (pinnedRows.getD 5 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow6 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 6) (pinnedRows.getD 6 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow7 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 7) (pinnedRows.getD 7 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow8 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 8) (pinnedRows.getD 8 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow9 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 9) (pinnedRows.getD 9 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow10 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 10) (pinnedRows.getD 10 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow11 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 11) (pinnedRows.getD 11 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow12 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 12) (pinnedRows.getD 12 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow13 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 13) (pinnedRows.getD 13 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow14 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 14) (pinnedRows.getD 14 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow15 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 15) (pinnedRows.getD 15 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow16 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 16) (pinnedRows.getD 16 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow17 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 17) (pinnedRows.getD 17 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow18 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 18) (pinnedRows.getD 18 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow19 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 19) (pinnedRows.getD 19 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow20 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 20) (pinnedRows.getD 20 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow21 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 21) (pinnedRows.getD 21 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow22 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 22) (pinnedRows.getD 22 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow23 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 23) (pinnedRows.getD 23 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow24 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 24) (pinnedRows.getD 24 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow25 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 25) (pinnedRows.getD 25 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow26 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 26) (pinnedRows.getD 26 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow27 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 27) (pinnedRows.getD 27 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow28 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 28) (pinnedRows.getD 28 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow29 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 29) (pinnedRows.getD 29 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow30 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 30) (pinnedRows.getD 30 (QI.pt 0)) = true := by decide +kernel
theorem pinnedRow31 : QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect 31) (pinnedRows.getD 31 (QI.pt 0)) = true := by decide +kernel

theorem pinnedRows_check (i : ℕ) (hi : i < 32) :
    QI.subset (rowI 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect i) (pinnedRows.getD i (QI.pt 0)) = true := by
  interval_cases i
  · exact pinnedRow0
  · exact pinnedRow1
  · exact pinnedRow2
  · exact pinnedRow3
  · exact pinnedRow4
  · exact pinnedRow5
  · exact pinnedRow6
  · exact pinnedRow7
  · exact pinnedRow8
  · exact pinnedRow9
  · exact pinnedRow10
  · exact pinnedRow11
  · exact pinnedRow12
  · exact pinnedRow13
  · exact pinnedRow14
  · exact pinnedRow15
  · exact pinnedRow16
  · exact pinnedRow17
  · exact pinnedRow18
  · exact pinnedRow19
  · exact pinnedRow20
  · exact pinnedRow21
  · exact pinnedRow22
  · exact pinnedRow23
  · exact pinnedRow24
  · exact pinnedRow25
  · exact pinnedRow26
  · exact pinnedRow27
  · exact pinnedRow28
  · exact pinnedRow29
  · exact pinnedRow30
  · exact pinnedRow31

def frequencyRows : List QI := [
  ⟨-21087513393/1000000000000, -21087475410/1000000000000⟩,
  ⟨-24143257037/1000000000000, -24143219151/1000000000000⟩,
  ⟨-26365011636/1000000000000, -26364973748/1000000000000⟩,
  ⟨-28103639456/1000000000000, -28103601564/1000000000000⟩,
  ⟨-29472627322/1000000000000, -29472589428/1000000000000⟩,
  ⟨-30524077142/1000000000000, -30524039246/1000000000000⟩,
  ⟨-31279373163/1000000000000, -31279335265/1000000000000⟩,
  ⟨-31733959834/1000000000000, -31733921933/1000000000000⟩,
  ⟨-31830692506/1000000000000, -31830654588/1000000000000⟩,
  ⟨-26617414322/1000000000000, -26617382185/1000000000000⟩,
  ⟨-22908107686/1000000000000, -22908079508/1000000000000⟩,
  ⟨-20669570433/1000000000000, -20669544523/1000000000000⟩,
  ⟨-18849432494/1000000000000, -18849408403/1000000000000⟩,
  ⟨-17343063486/1000000000000, -17343040874/1000000000000⟩,
  ⟨-16047780044/1000000000000, -16047758687/1000000000000⟩,
  ⟨-14912759773/1000000000000, -14912739505/1000000000000⟩,
  ⟨-13903574211/1000000000000, -13903554903/1000000000000⟩,
  ⟨-12995902329/1000000000000, -12995883879/1000000000000⟩,
  ⟨-12172878651/1000000000000, -12172860973/1000000000000⟩,
  ⟨-11421067976/1000000000000, -11421051001/1000000000000⟩,
  ⟨-10730701111/1000000000000, -10730684778/1000000000000⟩,
  ⟨-10093528658/1000000000000, -10093512917/1000000000000⟩,
  ⟨-9502925345/1000000000000, -9502910151/1000000000000⟩,
  ⟨-8953557535/1000000000000, -8953542849/1000000000000⟩,
  ⟨-8440935175/1000000000000, -8440920963/1000000000000⟩,
  ⟨-7961304666/1000000000000, -7961290897/1000000000000⟩,
  ⟨-7511207718/1000000000000, -7511194365/1000000000000⟩,
  ⟨-7088077545/1000000000000, -7088064583/1000000000000⟩,
  ⟨-6689502255/1000000000000, -6689489663/1000000000000⟩,
  ⟨-6313250091/1000000000000, -6313237848/1000000000000⟩,
  ⟨-5957582520/1000000000000, -5957570608/1000000000000⟩,
  ⟨-5620762441/1000000000000, -5620750873/1000000000000⟩,
  ⟨-5301452231/1000000000000, -5301441021/1000000000000⟩,
  ⟨-4998113971/1000000000000, -4998103073/1000000000000⟩,
  ⟨-4709826448/1000000000000, -4709815819/1000000000000⟩,
  ⟨-4435451605/1000000000000, -4435441233/1000000000000⟩,
  ⟨-4174128107/1000000000000, -4174117981/1000000000000⟩,
  ⟨-3924903574/1000000000000, -3924893685/1000000000000⟩,
  ⟨-3687015859/1000000000000, -3687006196/1000000000000⟩,
  ⟨-3459871340/1000000000000, -3459861895/1000000000000⟩,
  ⟨-3242687032/1000000000000, -3242677793/1000000000000⟩,
  ⟨-3034914755/1000000000000, -3034905707/1000000000000⟩,
  ⟨-2836025329/1000000000000, -2836016466/1000000000000⟩,
  ⟨-2645560404/1000000000000, -2645551723/1000000000000⟩,
  ⟨-2463059057/1000000000000, -2463050554/1000000000000⟩,
  ⟨-2288035853/1000000000000, -2288027522/1000000000000⟩,
  ⟨-2120089243/1000000000000, -2120081080/1000000000000⟩,
  ⟨-1958919004/1000000000000, -1958911004/1000000000000⟩,
  ⟨-1804254677/1000000000000, -1804246834/1000000000000⟩,
  ⟨-1655683323/1000000000000, -1655675633/1000000000000⟩,
  ⟨-1512940292/1000000000000, -1512932751/1000000000000⟩,
  ⟨-1375731668/1000000000000, -1375724273/1000000000000⟩,
  ⟨-1243871095/1000000000000, -1243863841/1000000000000⟩,
  ⟨-1117066635/1000000000000, -1117059518/1000000000000⟩,
  ⟨-995103194/1000000000000, -995096211/1000000000000⟩,
  ⟨-877810150/1000000000000, -877803298/1000000000000⟩,
  ⟨-764990606/1000000000000, -764983881/1000000000000⟩,
  ⟨-656435451/1000000000000, -656428850/1000000000000⟩,
  ⟨-552000753/1000000000000, -551994274/1000000000000⟩,
  ⟨-451525629/1000000000000, -451519268/1000000000000⟩,
  ⟨-354858356/1000000000000, -354852110/1000000000000⟩,
  ⟨-261850265/1000000000000, -261844133/1000000000000⟩,
  ⟨-172386984/1000000000000, -172380963/1000000000000⟩,
  ⟨-86329780/1000000000000, -86323868/1000000000000⟩,
  ⟨-3570754/1000000000000, -3564948/1000000000000⟩,
  ⟨76003674/1000000000000, 76009377/1000000000000⟩,
  ⟨152493556/1000000000000, 152499157/1000000000000⟩,
  ⟨226005201/1000000000000, 226010701/1000000000000⟩,
  ⟨296615879/1000000000000, 296621281/1000000000000⟩,
  ⟨364421007/1000000000000, 364426312/1000000000000⟩,
  ⟨429499185/1000000000000, 429504395/1000000000000⟩,
  ⟨491939439/1000000000000, 491944556/1000000000000⟩,
  ⟨551803182/1000000000000, 551808208/1000000000000⟩,
  ⟨609159666/1000000000000, 609164602/1000000000000⟩,
  ⟨664079792/1000000000000, 664084639/1000000000000⟩,
  ⟨716610551/1000000000000, 716615311/1000000000000⟩,
  ⟨766824130/1000000000000, 766828804/1000000000000⟩,
  ⟨814763923/1000000000000, 814768512/1000000000000⟩,
  ⟨860467094/1000000000000, 860471599/1000000000000⟩,
  ⟨904011421/1000000000000, 904015843/1000000000000⟩,
  ⟨945434918/1000000000000, 945439259/1000000000000⟩,
  ⟨984766139/1000000000000, 984770400/1000000000000⟩,
  ⟨1022055155/1000000000000, 1022059336/1000000000000⟩,
  ⟨1057328467/1000000000000, 1057332570/1000000000000⟩,
  ⟨1090625490/1000000000000, 1090629516/1000000000000⟩,
  ⟨1121969617/1000000000000, 1121973565/1000000000000⟩,
  ⟨1151395339/1000000000000, 1151399211/1000000000000⟩,
  ⟨1178920352/1000000000000, 1178924149/1000000000000⟩,
  ⟨1204569338/1000000000000, 1204573060/1000000000000⟩,
  ⟨1228361944/1000000000000, 1228365593/1000000000000⟩,
  ⟨1250312402/1000000000000, 1250315977/1000000000000⟩,
  ⟨1270434897/1000000000000, 1270438399/1000000000000⟩,
  ⟨1288752026/1000000000000, 1288755456/1000000000000⟩,
  ⟨1305295486/1000000000000, 1305298844/1000000000000⟩,
  ⟨1320046472/1000000000000, 1320049759/1000000000000⟩,
  ⟨1333010036/1000000000000, 1333013252/1000000000000⟩,
  ⟨1344172445/1000000000000, 1344175590/1000000000000⟩,
  ⟨1353540516/1000000000000, 1353543590/1000000000000⟩,
  ⟨1361112302/1000000000000, 1361115306/1000000000000⟩,
  ⟨1366858359/1000000000000, 1366861293/1000000000000⟩,
  ⟨1370788028/1000000000000, 1370790891/1000000000000⟩,
  ⟨1372918201/1000000000000, 1372920995/1000000000000⟩,
  ⟨1373170512/1000000000000, 1373173236/1000000000000⟩,
  ⟨1371572474/1000000000000, 1371575127/1000000000000⟩,
  ⟨1368055578/1000000000000, 1368058161/1000000000000⟩,
  ⟨1362593971/1000000000000, 1362596485/1000000000000⟩,
  ⟨1355123539/1000000000000, 1355125981/1000000000000⟩,
  ⟨1345588584/1000000000000, 1345590955/1000000000000⟩,
  ⟨1333951730/1000000000000, 1333954030/1000000000000⟩,
  ⟨1320175376/1000000000000, 1320177604/1000000000000⟩,
  ⟨1304095755/1000000000000, 1304097910/1000000000000⟩,
  ⟨1285707693/1000000000000, 1285709775/1000000000000⟩,
  ⟨1264778647/1000000000000, 1264780654/1000000000000⟩,
  ⟨1241348634/1000000000000, 1241350566/1000000000000⟩,
  ⟨1215067322/1000000000000, 1215069177/1000000000000⟩,
  ⟨1185863541/1000000000000, 1185865318/1000000000000⟩,
  ⟨1153472259/1000000000000, 1153473956/1000000000000⟩,
  ⟨1117582012/1000000000000, 1117583626/1000000000000⟩,
  ⟨1077930292/1000000000000, 1077931822/1000000000000⟩,
  ⟨1033964661/1000000000000, 1033966103/1000000000000⟩,
  ⟨985136988/1000000000000, 985138339/1000000000000⟩,
  ⟨930764626/1000000000000, 930765882/1000000000000⟩,
  ⟨869679485/1000000000000, 869680640/1000000000000⟩,
  ⟨800498313/1000000000000, 800499359/1000000000000⟩,
  ⟨720949012/1000000000000, 720949939/1000000000000⟩,
  ⟨627436597/1000000000000, 627437392/1000000000000⟩,
  ⟨510224173/1000000000000, 510224810/1000000000000⟩,
  ⟨366525583/1000000000000, 366526033/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩
]

theorem frequencyRow0 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 0) (frequencyRows.getD 0 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow1 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 1) (frequencyRows.getD 1 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow2 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 2) (frequencyRows.getD 2 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow3 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 3) (frequencyRows.getD 3 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow4 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 4) (frequencyRows.getD 4 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow5 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 5) (frequencyRows.getD 5 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow6 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 6) (frequencyRows.getD 6 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow7 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 7) (frequencyRows.getD 7 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow8 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 8) (frequencyRows.getD 8 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow9 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 9) (frequencyRows.getD 9 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow10 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 10) (frequencyRows.getD 10 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow11 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 11) (frequencyRows.getD 11 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow12 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 12) (frequencyRows.getD 12 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow13 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 13) (frequencyRows.getD 13 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow14 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 14) (frequencyRows.getD 14 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow15 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 15) (frequencyRows.getD 15 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow16 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 16) (frequencyRows.getD 16 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow17 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 17) (frequencyRows.getD 17 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow18 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 18) (frequencyRows.getD 18 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow19 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 19) (frequencyRows.getD 19 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow20 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 20) (frequencyRows.getD 20 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow21 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 21) (frequencyRows.getD 21 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow22 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 22) (frequencyRows.getD 22 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow23 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 23) (frequencyRows.getD 23 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow24 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 24) (frequencyRows.getD 24 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow25 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 25) (frequencyRows.getD 25 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow26 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 26) (frequencyRows.getD 26 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow27 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 27) (frequencyRows.getD 27 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow28 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 28) (frequencyRows.getD 28 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow29 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 29) (frequencyRows.getD 29 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow30 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 30) (frequencyRows.getD 30 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow31 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 31) (frequencyRows.getD 31 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow32 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 32) (frequencyRows.getD 32 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow33 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 33) (frequencyRows.getD 33 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow34 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 34) (frequencyRows.getD 34 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow35 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 35) (frequencyRows.getD 35 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow36 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 36) (frequencyRows.getD 36 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow37 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 37) (frequencyRows.getD 37 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow38 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 38) (frequencyRows.getD 38 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow39 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 39) (frequencyRows.getD 39 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow40 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 40) (frequencyRows.getD 40 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow41 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 41) (frequencyRows.getD 41 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow42 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 42) (frequencyRows.getD 42 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow43 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 43) (frequencyRows.getD 43 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow44 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 44) (frequencyRows.getD 44 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow45 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 45) (frequencyRows.getD 45 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow46 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 46) (frequencyRows.getD 46 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow47 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 47) (frequencyRows.getD 47 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow48 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 48) (frequencyRows.getD 48 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow49 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 49) (frequencyRows.getD 49 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow50 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 50) (frequencyRows.getD 50 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow51 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 51) (frequencyRows.getD 51 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow52 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 52) (frequencyRows.getD 52 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow53 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 53) (frequencyRows.getD 53 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow54 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 54) (frequencyRows.getD 54 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow55 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 55) (frequencyRows.getD 55 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow56 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 56) (frequencyRows.getD 56 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow57 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 57) (frequencyRows.getD 57 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow58 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 58) (frequencyRows.getD 58 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow59 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 59) (frequencyRows.getD 59 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow60 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 60) (frequencyRows.getD 60 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow61 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 61) (frequencyRows.getD 61 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow62 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 62) (frequencyRows.getD 62 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow63 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 63) (frequencyRows.getD 63 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow64 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 64) (frequencyRows.getD 64 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow65 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 65) (frequencyRows.getD 65 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow66 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 66) (frequencyRows.getD 66 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow67 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 67) (frequencyRows.getD 67 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow68 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 68) (frequencyRows.getD 68 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow69 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 69) (frequencyRows.getD 69 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow70 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 70) (frequencyRows.getD 70 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow71 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 71) (frequencyRows.getD 71 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow72 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 72) (frequencyRows.getD 72 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow73 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 73) (frequencyRows.getD 73 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow74 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 74) (frequencyRows.getD 74 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow75 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 75) (frequencyRows.getD 75 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow76 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 76) (frequencyRows.getD 76 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow77 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 77) (frequencyRows.getD 77 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow78 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 78) (frequencyRows.getD 78 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow79 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 79) (frequencyRows.getD 79 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow80 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 80) (frequencyRows.getD 80 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow81 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 81) (frequencyRows.getD 81 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow82 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 82) (frequencyRows.getD 82 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow83 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 83) (frequencyRows.getD 83 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow84 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 84) (frequencyRows.getD 84 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow85 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 85) (frequencyRows.getD 85 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow86 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 86) (frequencyRows.getD 86 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow87 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 87) (frequencyRows.getD 87 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow88 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 88) (frequencyRows.getD 88 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow89 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 89) (frequencyRows.getD 89 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow90 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 90) (frequencyRows.getD 90 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow91 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 91) (frequencyRows.getD 91 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow92 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 92) (frequencyRows.getD 92 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow93 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 93) (frequencyRows.getD 93 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow94 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 94) (frequencyRows.getD 94 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow95 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 95) (frequencyRows.getD 95 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow96 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 96) (frequencyRows.getD 96 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow97 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 97) (frequencyRows.getD 97 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow98 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 98) (frequencyRows.getD 98 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow99 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 99) (frequencyRows.getD 99 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow100 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 100) (frequencyRows.getD 100 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow101 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 101) (frequencyRows.getD 101 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow102 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 102) (frequencyRows.getD 102 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow103 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 103) (frequencyRows.getD 103 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow104 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 104) (frequencyRows.getD 104 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow105 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 105) (frequencyRows.getD 105 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow106 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 106) (frequencyRows.getD 106 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow107 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 107) (frequencyRows.getD 107 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow108 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 108) (frequencyRows.getD 108 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow109 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 109) (frequencyRows.getD 109 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow110 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 110) (frequencyRows.getD 110 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow111 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 111) (frequencyRows.getD 111 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow112 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 112) (frequencyRows.getD 112 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow113 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 113) (frequencyRows.getD 113 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow114 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 114) (frequencyRows.getD 114 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow115 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 115) (frequencyRows.getD 115 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow116 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 116) (frequencyRows.getD 116 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow117 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 117) (frequencyRows.getD 117 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow118 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 118) (frequencyRows.getD 118 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow119 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 119) (frequencyRows.getD 119 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow120 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 120) (frequencyRows.getD 120 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow121 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 121) (frequencyRows.getD 121 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow122 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 122) (frequencyRows.getD 122 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow123 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 123) (frequencyRows.getD 123 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow124 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 124) (frequencyRows.getD 124 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow125 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 125) (frequencyRows.getD 125 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow126 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 126) (frequencyRows.getD 126 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow127 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 127) (frequencyRows.getD 127 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow128 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 128) (frequencyRows.getD 128 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow129 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 129) (frequencyRows.getD 129 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow130 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 130) (frequencyRows.getD 130 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow131 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 131) (frequencyRows.getD 131 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow132 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 132) (frequencyRows.getD 132 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow133 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 133) (frequencyRows.getD 133 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow134 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 134) (frequencyRows.getD 134 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow135 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 135) (frequencyRows.getD 135 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow136 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 136) (frequencyRows.getD 136 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow137 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 137) (frequencyRows.getD 137 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow138 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 138) (frequencyRows.getD 138 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow139 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 139) (frequencyRows.getD 139 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow140 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 140) (frequencyRows.getD 140 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow141 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 141) (frequencyRows.getD 141 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow142 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 142) (frequencyRows.getD 142 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow143 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 143) (frequencyRows.getD 143 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow144 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 144) (frequencyRows.getD 144 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow145 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 145) (frequencyRows.getD 145 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow146 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 146) (frequencyRows.getD 146 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow147 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 147) (frequencyRows.getD 147 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow148 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 148) (frequencyRows.getD 148 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow149 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 149) (frequencyRows.getD 149 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow150 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 150) (frequencyRows.getD 150 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow151 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 151) (frequencyRows.getD 151 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow152 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 152) (frequencyRows.getD 152 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow153 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 153) (frequencyRows.getD 153 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow154 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 154) (frequencyRows.getD 154 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow155 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 155) (frequencyRows.getD 155 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow156 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 156) (frequencyRows.getD 156 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow157 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 157) (frequencyRows.getD 157 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow158 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 158) (frequencyRows.getD 158 (QI.pt 0)) = true := by decide +kernel
theorem frequencyRow159 : QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect 159) (frequencyRows.getD 159 (QI.pt 0)) = true := by decide +kernel

theorem frequencyRows_check (i : ℕ) (hi : i < 160) :
    QI.subset (rowI 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect i) (frequencyRows.getD i (QI.pt 0)) = true := by
  interval_cases i
  · exact frequencyRow0
  · exact frequencyRow1
  · exact frequencyRow2
  · exact frequencyRow3
  · exact frequencyRow4
  · exact frequencyRow5
  · exact frequencyRow6
  · exact frequencyRow7
  · exact frequencyRow8
  · exact frequencyRow9
  · exact frequencyRow10
  · exact frequencyRow11
  · exact frequencyRow12
  · exact frequencyRow13
  · exact frequencyRow14
  · exact frequencyRow15
  · exact frequencyRow16
  · exact frequencyRow17
  · exact frequencyRow18
  · exact frequencyRow19
  · exact frequencyRow20
  · exact frequencyRow21
  · exact frequencyRow22
  · exact frequencyRow23
  · exact frequencyRow24
  · exact frequencyRow25
  · exact frequencyRow26
  · exact frequencyRow27
  · exact frequencyRow28
  · exact frequencyRow29
  · exact frequencyRow30
  · exact frequencyRow31
  · exact frequencyRow32
  · exact frequencyRow33
  · exact frequencyRow34
  · exact frequencyRow35
  · exact frequencyRow36
  · exact frequencyRow37
  · exact frequencyRow38
  · exact frequencyRow39
  · exact frequencyRow40
  · exact frequencyRow41
  · exact frequencyRow42
  · exact frequencyRow43
  · exact frequencyRow44
  · exact frequencyRow45
  · exact frequencyRow46
  · exact frequencyRow47
  · exact frequencyRow48
  · exact frequencyRow49
  · exact frequencyRow50
  · exact frequencyRow51
  · exact frequencyRow52
  · exact frequencyRow53
  · exact frequencyRow54
  · exact frequencyRow55
  · exact frequencyRow56
  · exact frequencyRow57
  · exact frequencyRow58
  · exact frequencyRow59
  · exact frequencyRow60
  · exact frequencyRow61
  · exact frequencyRow62
  · exact frequencyRow63
  · exact frequencyRow64
  · exact frequencyRow65
  · exact frequencyRow66
  · exact frequencyRow67
  · exact frequencyRow68
  · exact frequencyRow69
  · exact frequencyRow70
  · exact frequencyRow71
  · exact frequencyRow72
  · exact frequencyRow73
  · exact frequencyRow74
  · exact frequencyRow75
  · exact frequencyRow76
  · exact frequencyRow77
  · exact frequencyRow78
  · exact frequencyRow79
  · exact frequencyRow80
  · exact frequencyRow81
  · exact frequencyRow82
  · exact frequencyRow83
  · exact frequencyRow84
  · exact frequencyRow85
  · exact frequencyRow86
  · exact frequencyRow87
  · exact frequencyRow88
  · exact frequencyRow89
  · exact frequencyRow90
  · exact frequencyRow91
  · exact frequencyRow92
  · exact frequencyRow93
  · exact frequencyRow94
  · exact frequencyRow95
  · exact frequencyRow96
  · exact frequencyRow97
  · exact frequencyRow98
  · exact frequencyRow99
  · exact frequencyRow100
  · exact frequencyRow101
  · exact frequencyRow102
  · exact frequencyRow103
  · exact frequencyRow104
  · exact frequencyRow105
  · exact frequencyRow106
  · exact frequencyRow107
  · exact frequencyRow108
  · exact frequencyRow109
  · exact frequencyRow110
  · exact frequencyRow111
  · exact frequencyRow112
  · exact frequencyRow113
  · exact frequencyRow114
  · exact frequencyRow115
  · exact frequencyRow116
  · exact frequencyRow117
  · exact frequencyRow118
  · exact frequencyRow119
  · exact frequencyRow120
  · exact frequencyRow121
  · exact frequencyRow122
  · exact frequencyRow123
  · exact frequencyRow124
  · exact frequencyRow125
  · exact frequencyRow126
  · exact frequencyRow127
  · exact frequencyRow128
  · exact frequencyRow129
  · exact frequencyRow130
  · exact frequencyRow131
  · exact frequencyRow132
  · exact frequencyRow133
  · exact frequencyRow134
  · exact frequencyRow135
  · exact frequencyRow136
  · exact frequencyRow137
  · exact frequencyRow138
  · exact frequencyRow139
  · exact frequencyRow140
  · exact frequencyRow141
  · exact frequencyRow142
  · exact frequencyRow143
  · exact frequencyRow144
  · exact frequencyRow145
  · exact frequencyRow146
  · exact frequencyRow147
  · exact frequencyRow148
  · exact frequencyRow149
  · exact frequencyRow150
  · exact frequencyRow151
  · exact frequencyRow152
  · exact frequencyRow153
  · exact frequencyRow154
  · exact frequencyRow155
  · exact frequencyRow156
  · exact frequencyRow157
  · exact frequencyRow158
  · exact frequencyRow159

def crossRows : List QI := [
  ⟨0/1000000000000, 1/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨0/1000000000000, 0/1000000000000⟩,
  ⟨1679820331/1000000000000, 1679824351/1000000000000⟩,
  ⟨5909149882/1000000000000, 5909163474/1000000000000⟩,
  ⟨7612080681/1000000000000, 7612097550/1000000000000⟩,
  ⟨9154430124/1000000000000, 9154449713/1000000000000⟩,
  ⟨10453319078/1000000000000, 10453340773/1000000000000⟩,
  ⟨11630735291/1000000000000, 11630758808/1000000000000⟩,
  ⟨12723606502/1000000000000, 12723631538/1000000000000⟩,
  ⟨13759660692/1000000000000, 13759687010/1000000000000⟩,
  ⟨14757884925/1000000000000, 14757912399/1000000000000⟩,
  ⟨15733001160/1000000000000, 15733029703/1000000000000⟩,
  ⟨16698870675/1000000000000, 16698900232/1000000000000⟩,
  ⟨17669622060/1000000000000, 17669652604/1000000000000⟩,
  ⟨18663200227/1000000000000, 18663231765/1000000000000⟩,
  ⟨19701478832/1000000000000, 19701511407/1000000000000⟩,
  ⟨20849151578/1000000000000, 20849185336/1000000000000⟩,
  ⟨22063996758/1000000000000, 22064031770/1000000000000⟩,
  ⟨24675468699/1000000000000, 24675507100/1000000000000⟩,
  ⟨25142801672/1000000000000, 25142840073/1000000000000⟩,
  ⟨25602554000/1000000000000, 25602592401/1000000000000⟩,
  ⟨26054983685/1000000000000, 26055022086/1000000000000⟩,
  ⟨26500335901/1000000000000, 26500374302/1000000000000⟩,
  ⟨26938842839/1000000000000, 26938881240/1000000000000⟩,
  ⟨27370725139/1000000000000, 27370763540/1000000000000⟩,
  ⟨27796192281/1000000000000, 27796230682/1000000000000⟩,
  ⟨28215443685/1000000000000, 28215482086/1000000000000⟩,
  ⟨28628669319/1000000000000, 28628707720/1000000000000⟩,
  ⟨29036050030/1000000000000, 29036088431/1000000000000⟩,
  ⟨29437758441/1000000000000, 29437796842/1000000000000⟩,
  ⟨29833959258/1000000000000, 29833997659/1000000000000⟩
]

theorem crossRow0 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 0) (crossRows.getD 0 (QI.pt 0)) = true := by decide +kernel
theorem crossRow1 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 1) (crossRows.getD 1 (QI.pt 0)) = true := by decide +kernel
theorem crossRow2 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 2) (crossRows.getD 2 (QI.pt 0)) = true := by decide +kernel
theorem crossRow3 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 3) (crossRows.getD 3 (QI.pt 0)) = true := by decide +kernel
theorem crossRow4 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 4) (crossRows.getD 4 (QI.pt 0)) = true := by decide +kernel
theorem crossRow5 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 5) (crossRows.getD 5 (QI.pt 0)) = true := by decide +kernel
theorem crossRow6 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 6) (crossRows.getD 6 (QI.pt 0)) = true := by decide +kernel
theorem crossRow7 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 7) (crossRows.getD 7 (QI.pt 0)) = true := by decide +kernel
theorem crossRow8 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 8) (crossRows.getD 8 (QI.pt 0)) = true := by decide +kernel
theorem crossRow9 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 9) (crossRows.getD 9 (QI.pt 0)) = true := by decide +kernel
theorem crossRow10 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 10) (crossRows.getD 10 (QI.pt 0)) = true := by decide +kernel
theorem crossRow11 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 11) (crossRows.getD 11 (QI.pt 0)) = true := by decide +kernel
theorem crossRow12 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 12) (crossRows.getD 12 (QI.pt 0)) = true := by decide +kernel
theorem crossRow13 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 13) (crossRows.getD 13 (QI.pt 0)) = true := by decide +kernel
theorem crossRow14 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 14) (crossRows.getD 14 (QI.pt 0)) = true := by decide +kernel
theorem crossRow15 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 15) (crossRows.getD 15 (QI.pt 0)) = true := by decide +kernel
theorem crossRow16 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 16) (crossRows.getD 16 (QI.pt 0)) = true := by decide +kernel
theorem crossRow17 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 17) (crossRows.getD 17 (QI.pt 0)) = true := by decide +kernel
theorem crossRow18 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 18) (crossRows.getD 18 (QI.pt 0)) = true := by decide +kernel
theorem crossRow19 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 19) (crossRows.getD 19 (QI.pt 0)) = true := by decide +kernel
theorem crossRow20 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 20) (crossRows.getD 20 (QI.pt 0)) = true := by decide +kernel
theorem crossRow21 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 21) (crossRows.getD 21 (QI.pt 0)) = true := by decide +kernel
theorem crossRow22 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 22) (crossRows.getD 22 (QI.pt 0)) = true := by decide +kernel
theorem crossRow23 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 23) (crossRows.getD 23 (QI.pt 0)) = true := by decide +kernel
theorem crossRow24 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 24) (crossRows.getD 24 (QI.pt 0)) = true := by decide +kernel
theorem crossRow25 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 25) (crossRows.getD 25 (QI.pt 0)) = true := by decide +kernel
theorem crossRow26 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 26) (crossRows.getD 26 (QI.pt 0)) = true := by decide +kernel
theorem crossRow27 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 27) (crossRows.getD 27 (QI.pt 0)) = true := by decide +kernel
theorem crossRow28 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 28) (crossRows.getD 28 (QI.pt 0)) = true := by decide +kernel
theorem crossRow29 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 29) (crossRows.getD 29 (QI.pt 0)) = true := by decide +kernel
theorem crossRow30 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 30) (crossRows.getD 30 (QI.pt 0)) = true := by decide +kernel
theorem crossRow31 : QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect 31) (crossRows.getD 31 (QI.pt 0)) = true := by decide +kernel

theorem crossRows_check (i : ℕ) (hi : i < 32) :
    QI.subset (rowI 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect i) (crossRows.getD i (QI.pt 0)) = true := by
  interval_cases i
  · exact crossRow0
  · exact crossRow1
  · exact crossRow2
  · exact crossRow3
  · exact crossRow4
  · exact crossRow5
  · exact crossRow6
  · exact crossRow7
  · exact crossRow8
  · exact crossRow9
  · exact crossRow10
  · exact crossRow11
  · exact crossRow12
  · exact crossRow13
  · exact crossRow14
  · exact crossRow15
  · exact crossRow16
  · exact crossRow17
  · exact crossRow18
  · exact crossRow19
  · exact crossRow20
  · exact crossRow21
  · exact crossRow22
  · exact crossRow23
  · exact crossRow24
  · exact crossRow25
  · exact crossRow26
  · exact crossRow27
  · exact crossRow28
  · exact crossRow29
  · exact crossRow30
  · exact crossRow31


theorem pinnedRows_sound : (rowsI 32 pinnedRows).Contains pinnedSelfEnergy := by
  rw [pinnedSelfEnergy, pinnedSelfEnergy_eq_rectangleSum]
  exact checkedRows_sound _ _ _ _ _ _ _ pinnedRows_check (fun i _ j _ => diffRect_sound (1/4) i j)

theorem frequencyRows_sound : (rowsI 160 frequencyRows).Contains frequencySelfEnergy := by
  rw [frequencySelfEnergy, frequencySelfEnergy_eq_rectangleSum]
  exact checkedRows_sound _ _ _ _ _ _ _ frequencyRows_check (fun i _ j _ => diffRect_sound (1/2) i j)

theorem crossRows_sound : (rowsI 32 crossRows).Contains pinnedFrequencyCross := by
  rw [pinnedFrequencyCross, pinnedReflectedFrequencyEnergy_eq_rectangleSum]
  exact checkedRows_sound _ _ _ _ _ _ _ crossRows_check (fun i _ j _ => plusRect_sound i j)

end Li2Lean.P0.ConfigRectangleBounds
