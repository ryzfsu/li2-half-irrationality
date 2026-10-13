/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigRectangleBase

namespace Li2Lean.P0.ConfigRectangleBounds
open Li2Lean.P0.CA.Pinned Li2Lean.LogSegment
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

def hTab : List QI := [
  ⟨-1/10000000000, 1/10000000000⟩,
  ⟨-24246759/10000000000, -24246756/10000000000⟩,
  ⟨-83449000/10000000000, -83448997/10000000000⟩,
  ⟨-169941957/10000000000, -169941954/10000000000⟩,
  ⟨-279643872/10000000000, -279643869/10000000000⟩,
  ⟨-409704346/10000000000, -409704343/10000000000⟩,
  ⟨-557925546/10000000000, -557925543/10000000000⟩,
  ⟨-722516905/10000000000, -722516902/10000000000⟩,
  ⟨-901966989/10000000000, -901966986/10000000000⟩,
  ⟨-1094967860/10000000000, -1094967857/10000000000⟩,
  ⟨-1300366608/10000000000, -1300366605/10000000000⟩,
  ⟨-1517132405/10000000000, -1517132402/10000000000⟩,
  ⟨-1744333070/10000000000, -1744333067/10000000000⟩,
  ⟨-1981117805/10000000000, -1981117802/10000000000⟩,
  ⟨-2226704105/10000000000, -2226704102/10000000000⟩,
  ⟨-2480367594/10000000000, -2480367591/10000000000⟩,
  ⟨-2741433977/10000000000, -2741433974/10000000000⟩,
  ⟨-3009272558/10000000000, -3009272555/10000000000⟩,
  ⟨-3283290934/10000000000, -3283290931/10000000000⟩,
  ⟨-3562930614/10000000000, -3562930611/10000000000⟩,
  ⟨-3847663340/10000000000, -3847663337/10000000000⟩,
  ⟨-4136987980/10000000000, -4136987977/10000000000⟩,
  ⟨-4430427880/10000000000, -4430427877/10000000000⟩,
  ⟨-4727528577/10000000000, -4727528574/10000000000⟩,
  ⟨-5027855830/10000000000, -5027855827/10000000000⟩,
  ⟨-5330993892/10000000000, -5330993889/10000000000⟩,
  ⟨-5636543999/10000000000, -5636543996/10000000000⟩,
  ⟨-5944123038/10000000000, -5944123035/10000000000⟩,
  ⟨-6253362364/10000000000, -6253362361/10000000000⟩,
  ⟨-6563906746/10000000000, -6563906743/10000000000⟩,
  ⟨-6875413424/10000000000, -6875413421/10000000000⟩,
  ⟨-7187551267/10000000000, -7187551264/10000000000⟩,
  ⟨-7500000001/10000000000, -7499999999/10000000000⟩,
  ⟨-7812449531/10000000000, -7812449528/10000000000⟩,
  ⟨-8124599304/10000000000, -8124599301/10000000000⟩,
  ⟨-8436157744/10000000000, -8436157741/10000000000⟩,
  ⟨-8746841729/10000000000, -8746841726/10000000000⟩,
  ⟨-9056376117/10000000000, -9056376114/10000000000⟩,
  ⟨-9364493307/10000000000, -9364493304/10000000000⟩,
  ⟨-9670932835/10000000000, -9670932832/10000000000⟩,
  ⟨-9975441007/10000000000, -9975441004/10000000000⟩,
  ⟨-10277770551/10000000000, -10277770548/10000000000⟩,
  ⟨-10577680304/10000000000, -10577680301/10000000000⟩,
  ⟨-10874934915/10000000000, -10874934912/10000000000⟩,
  ⟨-11169304575/10000000000, -11169304572/10000000000⟩,
  ⟨-11460564754/10000000000, -11460564751/10000000000⟩,
  ⟨-11748495975/10000000000, -11748495972/10000000000⟩,
  ⟨-12032883581/10000000000, -12032883578/10000000000⟩,
  ⟨-12313517535/10000000000, -12313517532/10000000000⟩,
  ⟨-12590192222/10000000000, -12590192219/10000000000⟩,
  ⟨-12862706268/10000000000, -12862706265/10000000000⟩,
  ⟨-13130862367/10000000000, -13130862364/10000000000⟩,
  ⟨-13394467121/10000000000, -13394467118/10000000000⟩,
  ⟨-13653330889/10000000000, -13653330886/10000000000⟩,
  ⟨-13907267642/10000000000, -13907267639/10000000000⟩,
  ⟨-14156094829/10000000000, -14156094826/10000000000⟩,
  ⟨-14399633249/10000000000, -14399633246/10000000000⟩,
  ⟨-14637706930/10000000000, -14637706927/10000000000⟩,
  ⟨-14870143017/10000000000, -14870143014/10000000000⟩,
  ⟨-15096771659/10000000000, -15096771656/10000000000⟩,
  ⟨-15317425910/10000000000, -15317425907/10000000000⟩,
  ⟨-15531941631/10000000000, -15531941628/10000000000⟩,
  ⟨-15740157395/10000000000, -15740157392/10000000000⟩,
  ⟨-15941914402/10000000000, -15941914399/10000000000⟩,
  ⟨-16137056390/10000000000, -16137056387/10000000000⟩,
  ⟨-16325429562/10000000000, -16325429559/10000000000⟩,
  ⟨-16506882503/10000000000, -16506882500/10000000000⟩,
  ⟨-16681266111/10000000000, -16681266108/10000000000⟩,
  ⟨-16848433526/10000000000, -16848433523/10000000000⟩,
  ⟨-17008240064/10000000000, -17008240061/10000000000⟩,
  ⟨-17160543154/10000000000, -17160543151/10000000000⟩,
  ⟨-17305202276/10000000000, -17305202273/10000000000⟩,
  ⟨-17442078904/10000000000, -17442078901/10000000000⟩,
  ⟨-17571036447/10000000000, -17571036444/10000000000⟩,
  ⟨-17691940203/10000000000, -17691940200/10000000000⟩,
  ⟨-17804657299/10000000000, -17804657296/10000000000⟩,
  ⟨-17909056647/10000000000, -17909056644/10000000000⟩,
  ⟨-18005008896/10000000000, -18005008893/10000000000⟩,
  ⟨-18092386384/10000000000, -18092386381/10000000000⟩,
  ⟨-18171063098/10000000000, -18171063095/10000000000⟩,
  ⟨-18240914630/10000000000, -18240914627/10000000000⟩,
  ⟨-18301818139/10000000000, -18301818136/10000000000⟩,
  ⟨-18353652305/10000000000, -18353652302/10000000000⟩,
  ⟨-18396297303/10000000000, -18396297300/10000000000⟩,
  ⟨-18429634755/10000000000, -18429634752/10000000000⟩,
  ⟨-18453547705/10000000000, -18453547702/10000000000⟩,
  ⟨-18467920578/10000000000, -18467920575/10000000000⟩,
  ⟨-18472639153/10000000000, -18472639150/10000000000⟩,
  ⟨-18467590529/10000000000, -18467590526/10000000000⟩,
  ⟨-18452663094/10000000000, -18452663091/10000000000⟩,
  ⟨-18427746501/10000000000, -18427746498/10000000000⟩,
  ⟨-18392731630/10000000000, -18392731627/10000000000⟩,
  ⟨-18347510574/10000000000, -18347510571/10000000000⟩,
  ⟨-18291976598/10000000000, -18291976595/10000000000⟩,
  ⟨-18226024127/10000000000, -18226024124/10000000000⟩,
  ⟨-18149548713/10000000000, -18149548710/10000000000⟩,
  ⟨-18062447011/10000000000, -18062447008/10000000000⟩,
  ⟨-17964616763/10000000000, -17964616760/10000000000⟩,
  ⟨-17855956766/10000000000, -17855956763/10000000000⟩,
  ⟨-17736366858/10000000000, -17736366855/10000000000⟩,
  ⟨-17605747893/10000000000, -17605747890/10000000000⟩,
  ⟨-17464001721/10000000000, -17464001718/10000000000⟩,
  ⟨-17311031170/10000000000, -17311031167/10000000000⟩,
  ⟨-17146740024/10000000000, -17146740021/10000000000⟩,
  ⟨-16971033007/10000000000, -16971033004/10000000000⟩,
  ⟨-16783815763/10000000000, -16783815760/10000000000⟩,
  ⟨-16584994838/10000000000, -16584994835/10000000000⟩,
  ⟨-16374477665/10000000000, -16374477662/10000000000⟩,
  ⟨-16152172546/10000000000, -16152172543/10000000000⟩,
  ⟨-15917988636/10000000000, -15917988633/10000000000⟩,
  ⟨-15671835928/10000000000, -15671835925/10000000000⟩,
  ⟨-15413625236/10000000000, -15413625233/10000000000⟩,
  ⟨-15143268181/10000000000, -15143268178/10000000000⟩,
  ⟨-14860677178/10000000000, -14860677175/10000000000⟩,
  ⟨-14565765419/10000000000, -14565765416/10000000000⟩,
  ⟨-14258446861/10000000000, -14258446858/10000000000⟩,
  ⟨-13938636215/10000000000, -13938636212/10000000000⟩,
  ⟨-13606248927/10000000000, -13606248924/10000000000⟩,
  ⟨-13261201171/10000000000, -13261201168/10000000000⟩,
  ⟨-12903409834/10000000000, -12903409831/10000000000⟩,
  ⟨-12532792503/10000000000, -12532792500/10000000000⟩,
  ⟨-12149267457/10000000000, -12149267454/10000000000⟩,
  ⟨-11752753651/10000000000, -11752753648/10000000000⟩,
  ⟨-11343170710/10000000000, -11343170707/10000000000⟩,
  ⟨-10920438911/10000000000, -10920438908/10000000000⟩,
  ⟨-10484479181/10000000000, -10484479178/10000000000⟩,
  ⟨-10035213078/10000000000, -10035213075/10000000000⟩,
  ⟨-9572562788/10000000000, -9572562785/10000000000⟩,
  ⟨-9096451112/10000000000, -9096451109/10000000000⟩,
  ⟨-8606801454/10000000000, -8606801451/10000000000⟩,
  ⟨-8103537817/10000000000, -8103537814/10000000000⟩,
  ⟨-7586584789/10000000000, -7586584786/10000000000⟩,
  ⟨-7055867537/10000000000, -7055867534/10000000000⟩,
  ⟨-6511311796/10000000000, -6511311793/10000000000⟩,
  ⟨-5952843863/10000000000, -5952843860/10000000000⟩,
  ⟨-5380390585/10000000000, -5380390582/10000000000⟩,
  ⟨-4793879355/10000000000, -4793879352/10000000000⟩,
  ⟨-4193238101/10000000000, -4193238098/10000000000⟩,
  ⟨-3578395279/10000000000, -3578395276/10000000000⟩,
  ⟨-2949279865/10000000000, -2949279862/10000000000⟩,
  ⟨-2305821348/10000000000, -2305821345/10000000000⟩,
  ⟨-1647949723/10000000000, -1647949720/10000000000⟩,
  ⟨-975595483/10000000000, -975595480/10000000000⟩,
  ⟨-288689612/10000000000, -288689609/10000000000⟩,
  ⟨412836422/10000000000, 412836425/10000000000⟩,
  ⟨1129050672/10000000000, 1129050675/10000000000⟩,
  ⟨1860020722/10000000000, 1860020725/10000000000⟩,
  ⟨2605813690/10000000000, 2605813693/10000000000⟩,
  ⟨3366496237/10000000000, 3366496240/10000000000⟩,
  ⟨4142134570/10000000000, 4142134573/10000000000⟩,
  ⟨4932794452/10000000000, 4932794455/10000000000⟩,
  ⟨5738541207/10000000000, 5738541210/10000000000⟩,
  ⟨6559439722/10000000000, 6559439725/10000000000⟩,
  ⟨7395554458/10000000000, 7395554461/10000000000⟩,
  ⟨8246949452/10000000000, 8246949455/10000000000⟩,
  ⟨9113688325/10000000000, 9113688328/10000000000⟩,
  ⟨9995834285/10000000000, 9995834288/10000000000⟩,
  ⟨10893450135/10000000000, 10893450138/10000000000⟩,
  ⟨11806598275/10000000000, 11806598278/10000000000⟩,
  ⟨12735340710/10000000000, 12735340713/10000000000⟩,
  ⟨13679739053/10000000000, 13679739056/10000000000⟩,
  ⟨14639854531/10000000000, 14639854534/10000000000⟩,
  ⟨15615747991/10000000000, 15615747994/10000000000⟩,
  ⟨16607479900/10000000000, 16607479903/10000000000⟩,
  ⟨17615110355/10000000000, 17615110358/10000000000⟩,
  ⟨18638699086/10000000000, 18638699089/10000000000⟩,
  ⟨19678305459/10000000000, 19678305462/10000000000⟩,
  ⟨20733988481/10000000000, 20733988484/10000000000⟩,
  ⟨21805806805/10000000000, 21805806808/10000000000⟩,
  ⟨22893818734/10000000000, 22893818737/10000000000⟩,
  ⟨23998082224/10000000000, 23998082227/10000000000⟩,
  ⟨25118654891/10000000000, 25118654894/10000000000⟩,
  ⟨26255594010/10000000000, 26255594013/10000000000⟩,
  ⟨27408956526/10000000000, 27408956529/10000000000⟩,
  ⟨28578799051/10000000000, 28578799054/10000000000⟩,
  ⟨29765177870/10000000000, 29765177873/10000000000⟩,
  ⟨30968148950/10000000000, 30968148953/10000000000⟩,
  ⟨32187767933/10000000000, 32187767936/10000000000⟩,
  ⟨33424090151/10000000000, 33424090154/10000000000⟩,
  ⟨34677170620/10000000000, 34677170623/10000000000⟩,
  ⟨35947064052/10000000000, 35947064055/10000000000⟩,
  ⟨37233824850/10000000000, 37233824853/10000000000⟩,
  ⟨38537507120/10000000000, 38537507123/10000000000⟩,
  ⟨39858164665/10000000000, 39858164668/10000000000⟩,
  ⟨41195850997/10000000000, 41195851000/10000000000⟩,
  ⟨42550619334/10000000000, 42550619337/10000000000⟩,
  ⟨43922522608/10000000000, 43922522611/10000000000⟩,
  ⟨45311613464/10000000000, 45311613467/10000000000⟩,
  ⟨46717944265/10000000000, 46717944268/10000000000⟩,
  ⟨48141567093/10000000000, 48141567096/10000000000⟩,
  ⟨49582533758/10000000000, 49582533761/10000000000⟩,
  ⟨51040895792/10000000000, 51040895795/10000000000⟩,
  ⟨52516704460/10000000000, 52516704463/10000000000⟩,
  ⟨54010010756/10000000000, 54010010759/10000000000⟩,
  ⟨55520865412/10000000000, 55520865415/10000000000⟩,
  ⟨57049318897/10000000000, 57049318900/10000000000⟩,
  ⟨58595421420/10000000000, 58595421423/10000000000⟩,
  ⟨60159222932/10000000000, 60159222935/10000000000⟩,
  ⟨61740773133/10000000000, 61740773136/10000000000⟩,
  ⟨63340121469/10000000000, 63340121472/10000000000⟩,
  ⟨64957317137/10000000000, 64957317140/10000000000⟩,
  ⟨66592409088/10000000000, 66592409091/10000000000⟩,
  ⟨68245446028/10000000000, 68245446031/10000000000⟩,
  ⟨69916476424/10000000000, 69916476427/10000000000⟩,
  ⟨71605548499/10000000000, 71605548502/10000000000⟩,
  ⟨73312710243/10000000000, 73312710246/10000000000⟩,
  ⟨75038009410/10000000000, 75038009413/10000000000⟩,
  ⟨76781493522/10000000000, 76781493525/10000000000⟩,
  ⟨78543209869/10000000000, 78543209872/10000000000⟩,
  ⟨80323205515/10000000000, 80323205518/10000000000⟩,
  ⟨82121527299/10000000000, 82121527302/10000000000⟩,
  ⟨83938221834/10000000000, 83938221837/10000000000⟩,
  ⟨85773335513/10000000000, 85773335516/10000000000⟩,
  ⟨87626914510/10000000000, 87626914513/10000000000⟩,
  ⟨89499004780/10000000000, 89499004783/10000000000⟩,
  ⟨91389652065/10000000000, 91389652068/10000000000⟩,
  ⟨93298901892/10000000000, 93298901895/10000000000⟩
]

theorem hCheck0 : QI.subset (HI (0/32)) (hTab.getD 0 (QI.pt 0)) = true := by decide +kernel
theorem hCheck1 : QI.subset (HI (1/32)) (hTab.getD 1 (QI.pt 0)) = true := by decide +kernel
theorem hCheck2 : QI.subset (HI (2/32)) (hTab.getD 2 (QI.pt 0)) = true := by decide +kernel
theorem hCheck3 : QI.subset (HI (3/32)) (hTab.getD 3 (QI.pt 0)) = true := by decide +kernel
theorem hCheck4 : QI.subset (HI (4/32)) (hTab.getD 4 (QI.pt 0)) = true := by decide +kernel
theorem hCheck5 : QI.subset (HI (5/32)) (hTab.getD 5 (QI.pt 0)) = true := by decide +kernel
theorem hCheck6 : QI.subset (HI (6/32)) (hTab.getD 6 (QI.pt 0)) = true := by decide +kernel
theorem hCheck7 : QI.subset (HI (7/32)) (hTab.getD 7 (QI.pt 0)) = true := by decide +kernel
theorem hCheck8 : QI.subset (HI (8/32)) (hTab.getD 8 (QI.pt 0)) = true := by decide +kernel
theorem hCheck9 : QI.subset (HI (9/32)) (hTab.getD 9 (QI.pt 0)) = true := by decide +kernel
theorem hCheck10 : QI.subset (HI (10/32)) (hTab.getD 10 (QI.pt 0)) = true := by decide +kernel
theorem hCheck11 : QI.subset (HI (11/32)) (hTab.getD 11 (QI.pt 0)) = true := by decide +kernel
theorem hCheck12 : QI.subset (HI (12/32)) (hTab.getD 12 (QI.pt 0)) = true := by decide +kernel
theorem hCheck13 : QI.subset (HI (13/32)) (hTab.getD 13 (QI.pt 0)) = true := by decide +kernel
theorem hCheck14 : QI.subset (HI (14/32)) (hTab.getD 14 (QI.pt 0)) = true := by decide +kernel
theorem hCheck15 : QI.subset (HI (15/32)) (hTab.getD 15 (QI.pt 0)) = true := by decide +kernel
theorem hCheck16 : QI.subset (HI (16/32)) (hTab.getD 16 (QI.pt 0)) = true := by decide +kernel
theorem hCheck17 : QI.subset (HI (17/32)) (hTab.getD 17 (QI.pt 0)) = true := by decide +kernel
theorem hCheck18 : QI.subset (HI (18/32)) (hTab.getD 18 (QI.pt 0)) = true := by decide +kernel
theorem hCheck19 : QI.subset (HI (19/32)) (hTab.getD 19 (QI.pt 0)) = true := by decide +kernel
theorem hCheck20 : QI.subset (HI (20/32)) (hTab.getD 20 (QI.pt 0)) = true := by decide +kernel
theorem hCheck21 : QI.subset (HI (21/32)) (hTab.getD 21 (QI.pt 0)) = true := by decide +kernel
theorem hCheck22 : QI.subset (HI (22/32)) (hTab.getD 22 (QI.pt 0)) = true := by decide +kernel
theorem hCheck23 : QI.subset (HI (23/32)) (hTab.getD 23 (QI.pt 0)) = true := by decide +kernel
theorem hCheck24 : QI.subset (HI (24/32)) (hTab.getD 24 (QI.pt 0)) = true := by decide +kernel
theorem hCheck25 : QI.subset (HI (25/32)) (hTab.getD 25 (QI.pt 0)) = true := by decide +kernel
theorem hCheck26 : QI.subset (HI (26/32)) (hTab.getD 26 (QI.pt 0)) = true := by decide +kernel
theorem hCheck27 : QI.subset (HI (27/32)) (hTab.getD 27 (QI.pt 0)) = true := by decide +kernel
theorem hCheck28 : QI.subset (HI (28/32)) (hTab.getD 28 (QI.pt 0)) = true := by decide +kernel
theorem hCheck29 : QI.subset (HI (29/32)) (hTab.getD 29 (QI.pt 0)) = true := by decide +kernel
theorem hCheck30 : QI.subset (HI (30/32)) (hTab.getD 30 (QI.pt 0)) = true := by decide +kernel
theorem hCheck31 : QI.subset (HI (31/32)) (hTab.getD 31 (QI.pt 0)) = true := by decide +kernel
theorem hCheck32 : QI.subset (HI (32/32)) (hTab.getD 32 (QI.pt 0)) = true := by decide +kernel
theorem hCheck33 : QI.subset (HI (33/32)) (hTab.getD 33 (QI.pt 0)) = true := by decide +kernel
theorem hCheck34 : QI.subset (HI (34/32)) (hTab.getD 34 (QI.pt 0)) = true := by decide +kernel
theorem hCheck35 : QI.subset (HI (35/32)) (hTab.getD 35 (QI.pt 0)) = true := by decide +kernel
theorem hCheck36 : QI.subset (HI (36/32)) (hTab.getD 36 (QI.pt 0)) = true := by decide +kernel
theorem hCheck37 : QI.subset (HI (37/32)) (hTab.getD 37 (QI.pt 0)) = true := by decide +kernel
theorem hCheck38 : QI.subset (HI (38/32)) (hTab.getD 38 (QI.pt 0)) = true := by decide +kernel
theorem hCheck39 : QI.subset (HI (39/32)) (hTab.getD 39 (QI.pt 0)) = true := by decide +kernel
theorem hCheck40 : QI.subset (HI (40/32)) (hTab.getD 40 (QI.pt 0)) = true := by decide +kernel
theorem hCheck41 : QI.subset (HI (41/32)) (hTab.getD 41 (QI.pt 0)) = true := by decide +kernel
theorem hCheck42 : QI.subset (HI (42/32)) (hTab.getD 42 (QI.pt 0)) = true := by decide +kernel
theorem hCheck43 : QI.subset (HI (43/32)) (hTab.getD 43 (QI.pt 0)) = true := by decide +kernel
theorem hCheck44 : QI.subset (HI (44/32)) (hTab.getD 44 (QI.pt 0)) = true := by decide +kernel
theorem hCheck45 : QI.subset (HI (45/32)) (hTab.getD 45 (QI.pt 0)) = true := by decide +kernel
theorem hCheck46 : QI.subset (HI (46/32)) (hTab.getD 46 (QI.pt 0)) = true := by decide +kernel
theorem hCheck47 : QI.subset (HI (47/32)) (hTab.getD 47 (QI.pt 0)) = true := by decide +kernel
theorem hCheck48 : QI.subset (HI (48/32)) (hTab.getD 48 (QI.pt 0)) = true := by decide +kernel
theorem hCheck49 : QI.subset (HI (49/32)) (hTab.getD 49 (QI.pt 0)) = true := by decide +kernel
theorem hCheck50 : QI.subset (HI (50/32)) (hTab.getD 50 (QI.pt 0)) = true := by decide +kernel
theorem hCheck51 : QI.subset (HI (51/32)) (hTab.getD 51 (QI.pt 0)) = true := by decide +kernel
theorem hCheck52 : QI.subset (HI (52/32)) (hTab.getD 52 (QI.pt 0)) = true := by decide +kernel
theorem hCheck53 : QI.subset (HI (53/32)) (hTab.getD 53 (QI.pt 0)) = true := by decide +kernel
theorem hCheck54 : QI.subset (HI (54/32)) (hTab.getD 54 (QI.pt 0)) = true := by decide +kernel
theorem hCheck55 : QI.subset (HI (55/32)) (hTab.getD 55 (QI.pt 0)) = true := by decide +kernel
theorem hCheck56 : QI.subset (HI (56/32)) (hTab.getD 56 (QI.pt 0)) = true := by decide +kernel
theorem hCheck57 : QI.subset (HI (57/32)) (hTab.getD 57 (QI.pt 0)) = true := by decide +kernel
theorem hCheck58 : QI.subset (HI (58/32)) (hTab.getD 58 (QI.pt 0)) = true := by decide +kernel
theorem hCheck59 : QI.subset (HI (59/32)) (hTab.getD 59 (QI.pt 0)) = true := by decide +kernel
theorem hCheck60 : QI.subset (HI (60/32)) (hTab.getD 60 (QI.pt 0)) = true := by decide +kernel
theorem hCheck61 : QI.subset (HI (61/32)) (hTab.getD 61 (QI.pt 0)) = true := by decide +kernel
theorem hCheck62 : QI.subset (HI (62/32)) (hTab.getD 62 (QI.pt 0)) = true := by decide +kernel
theorem hCheck63 : QI.subset (HI (63/32)) (hTab.getD 63 (QI.pt 0)) = true := by decide +kernel
theorem hCheck64 : QI.subset (HI (64/32)) (hTab.getD 64 (QI.pt 0)) = true := by decide +kernel
theorem hCheck65 : QI.subset (HI (65/32)) (hTab.getD 65 (QI.pt 0)) = true := by decide +kernel
theorem hCheck66 : QI.subset (HI (66/32)) (hTab.getD 66 (QI.pt 0)) = true := by decide +kernel
theorem hCheck67 : QI.subset (HI (67/32)) (hTab.getD 67 (QI.pt 0)) = true := by decide +kernel
theorem hCheck68 : QI.subset (HI (68/32)) (hTab.getD 68 (QI.pt 0)) = true := by decide +kernel
theorem hCheck69 : QI.subset (HI (69/32)) (hTab.getD 69 (QI.pt 0)) = true := by decide +kernel
theorem hCheck70 : QI.subset (HI (70/32)) (hTab.getD 70 (QI.pt 0)) = true := by decide +kernel
theorem hCheck71 : QI.subset (HI (71/32)) (hTab.getD 71 (QI.pt 0)) = true := by decide +kernel
theorem hCheck72 : QI.subset (HI (72/32)) (hTab.getD 72 (QI.pt 0)) = true := by decide +kernel
theorem hCheck73 : QI.subset (HI (73/32)) (hTab.getD 73 (QI.pt 0)) = true := by decide +kernel
theorem hCheck74 : QI.subset (HI (74/32)) (hTab.getD 74 (QI.pt 0)) = true := by decide +kernel
theorem hCheck75 : QI.subset (HI (75/32)) (hTab.getD 75 (QI.pt 0)) = true := by decide +kernel
theorem hCheck76 : QI.subset (HI (76/32)) (hTab.getD 76 (QI.pt 0)) = true := by decide +kernel
theorem hCheck77 : QI.subset (HI (77/32)) (hTab.getD 77 (QI.pt 0)) = true := by decide +kernel
theorem hCheck78 : QI.subset (HI (78/32)) (hTab.getD 78 (QI.pt 0)) = true := by decide +kernel
theorem hCheck79 : QI.subset (HI (79/32)) (hTab.getD 79 (QI.pt 0)) = true := by decide +kernel
theorem hCheck80 : QI.subset (HI (80/32)) (hTab.getD 80 (QI.pt 0)) = true := by decide +kernel
theorem hCheck81 : QI.subset (HI (81/32)) (hTab.getD 81 (QI.pt 0)) = true := by decide +kernel
theorem hCheck82 : QI.subset (HI (82/32)) (hTab.getD 82 (QI.pt 0)) = true := by decide +kernel
theorem hCheck83 : QI.subset (HI (83/32)) (hTab.getD 83 (QI.pt 0)) = true := by decide +kernel
theorem hCheck84 : QI.subset (HI (84/32)) (hTab.getD 84 (QI.pt 0)) = true := by decide +kernel
theorem hCheck85 : QI.subset (HI (85/32)) (hTab.getD 85 (QI.pt 0)) = true := by decide +kernel
theorem hCheck86 : QI.subset (HI (86/32)) (hTab.getD 86 (QI.pt 0)) = true := by decide +kernel
theorem hCheck87 : QI.subset (HI (87/32)) (hTab.getD 87 (QI.pt 0)) = true := by decide +kernel
theorem hCheck88 : QI.subset (HI (88/32)) (hTab.getD 88 (QI.pt 0)) = true := by decide +kernel
theorem hCheck89 : QI.subset (HI (89/32)) (hTab.getD 89 (QI.pt 0)) = true := by decide +kernel
theorem hCheck90 : QI.subset (HI (90/32)) (hTab.getD 90 (QI.pt 0)) = true := by decide +kernel
theorem hCheck91 : QI.subset (HI (91/32)) (hTab.getD 91 (QI.pt 0)) = true := by decide +kernel
theorem hCheck92 : QI.subset (HI (92/32)) (hTab.getD 92 (QI.pt 0)) = true := by decide +kernel
theorem hCheck93 : QI.subset (HI (93/32)) (hTab.getD 93 (QI.pt 0)) = true := by decide +kernel
theorem hCheck94 : QI.subset (HI (94/32)) (hTab.getD 94 (QI.pt 0)) = true := by decide +kernel
theorem hCheck95 : QI.subset (HI (95/32)) (hTab.getD 95 (QI.pt 0)) = true := by decide +kernel
theorem hCheck96 : QI.subset (HI (96/32)) (hTab.getD 96 (QI.pt 0)) = true := by decide +kernel
theorem hCheck97 : QI.subset (HI (97/32)) (hTab.getD 97 (QI.pt 0)) = true := by decide +kernel
theorem hCheck98 : QI.subset (HI (98/32)) (hTab.getD 98 (QI.pt 0)) = true := by decide +kernel
theorem hCheck99 : QI.subset (HI (99/32)) (hTab.getD 99 (QI.pt 0)) = true := by decide +kernel
theorem hCheck100 : QI.subset (HI (100/32)) (hTab.getD 100 (QI.pt 0)) = true := by decide +kernel
theorem hCheck101 : QI.subset (HI (101/32)) (hTab.getD 101 (QI.pt 0)) = true := by decide +kernel
theorem hCheck102 : QI.subset (HI (102/32)) (hTab.getD 102 (QI.pt 0)) = true := by decide +kernel
theorem hCheck103 : QI.subset (HI (103/32)) (hTab.getD 103 (QI.pt 0)) = true := by decide +kernel
theorem hCheck104 : QI.subset (HI (104/32)) (hTab.getD 104 (QI.pt 0)) = true := by decide +kernel
theorem hCheck105 : QI.subset (HI (105/32)) (hTab.getD 105 (QI.pt 0)) = true := by decide +kernel
theorem hCheck106 : QI.subset (HI (106/32)) (hTab.getD 106 (QI.pt 0)) = true := by decide +kernel
theorem hCheck107 : QI.subset (HI (107/32)) (hTab.getD 107 (QI.pt 0)) = true := by decide +kernel
theorem hCheck108 : QI.subset (HI (108/32)) (hTab.getD 108 (QI.pt 0)) = true := by decide +kernel
theorem hCheck109 : QI.subset (HI (109/32)) (hTab.getD 109 (QI.pt 0)) = true := by decide +kernel
theorem hCheck110 : QI.subset (HI (110/32)) (hTab.getD 110 (QI.pt 0)) = true := by decide +kernel
theorem hCheck111 : QI.subset (HI (111/32)) (hTab.getD 111 (QI.pt 0)) = true := by decide +kernel
theorem hCheck112 : QI.subset (HI (112/32)) (hTab.getD 112 (QI.pt 0)) = true := by decide +kernel
theorem hCheck113 : QI.subset (HI (113/32)) (hTab.getD 113 (QI.pt 0)) = true := by decide +kernel
theorem hCheck114 : QI.subset (HI (114/32)) (hTab.getD 114 (QI.pt 0)) = true := by decide +kernel
theorem hCheck115 : QI.subset (HI (115/32)) (hTab.getD 115 (QI.pt 0)) = true := by decide +kernel
theorem hCheck116 : QI.subset (HI (116/32)) (hTab.getD 116 (QI.pt 0)) = true := by decide +kernel
theorem hCheck117 : QI.subset (HI (117/32)) (hTab.getD 117 (QI.pt 0)) = true := by decide +kernel
theorem hCheck118 : QI.subset (HI (118/32)) (hTab.getD 118 (QI.pt 0)) = true := by decide +kernel
theorem hCheck119 : QI.subset (HI (119/32)) (hTab.getD 119 (QI.pt 0)) = true := by decide +kernel
theorem hCheck120 : QI.subset (HI (120/32)) (hTab.getD 120 (QI.pt 0)) = true := by decide +kernel
theorem hCheck121 : QI.subset (HI (121/32)) (hTab.getD 121 (QI.pt 0)) = true := by decide +kernel
theorem hCheck122 : QI.subset (HI (122/32)) (hTab.getD 122 (QI.pt 0)) = true := by decide +kernel
theorem hCheck123 : QI.subset (HI (123/32)) (hTab.getD 123 (QI.pt 0)) = true := by decide +kernel
theorem hCheck124 : QI.subset (HI (124/32)) (hTab.getD 124 (QI.pt 0)) = true := by decide +kernel
theorem hCheck125 : QI.subset (HI (125/32)) (hTab.getD 125 (QI.pt 0)) = true := by decide +kernel
theorem hCheck126 : QI.subset (HI (126/32)) (hTab.getD 126 (QI.pt 0)) = true := by decide +kernel
theorem hCheck127 : QI.subset (HI (127/32)) (hTab.getD 127 (QI.pt 0)) = true := by decide +kernel
theorem hCheck128 : QI.subset (HI (128/32)) (hTab.getD 128 (QI.pt 0)) = true := by decide +kernel
theorem hCheck129 : QI.subset (HI (129/32)) (hTab.getD 129 (QI.pt 0)) = true := by decide +kernel
theorem hCheck130 : QI.subset (HI (130/32)) (hTab.getD 130 (QI.pt 0)) = true := by decide +kernel
theorem hCheck131 : QI.subset (HI (131/32)) (hTab.getD 131 (QI.pt 0)) = true := by decide +kernel
theorem hCheck132 : QI.subset (HI (132/32)) (hTab.getD 132 (QI.pt 0)) = true := by decide +kernel
theorem hCheck133 : QI.subset (HI (133/32)) (hTab.getD 133 (QI.pt 0)) = true := by decide +kernel
theorem hCheck134 : QI.subset (HI (134/32)) (hTab.getD 134 (QI.pt 0)) = true := by decide +kernel
theorem hCheck135 : QI.subset (HI (135/32)) (hTab.getD 135 (QI.pt 0)) = true := by decide +kernel
theorem hCheck136 : QI.subset (HI (136/32)) (hTab.getD 136 (QI.pt 0)) = true := by decide +kernel
theorem hCheck137 : QI.subset (HI (137/32)) (hTab.getD 137 (QI.pt 0)) = true := by decide +kernel
theorem hCheck138 : QI.subset (HI (138/32)) (hTab.getD 138 (QI.pt 0)) = true := by decide +kernel
theorem hCheck139 : QI.subset (HI (139/32)) (hTab.getD 139 (QI.pt 0)) = true := by decide +kernel
theorem hCheck140 : QI.subset (HI (140/32)) (hTab.getD 140 (QI.pt 0)) = true := by decide +kernel
theorem hCheck141 : QI.subset (HI (141/32)) (hTab.getD 141 (QI.pt 0)) = true := by decide +kernel
theorem hCheck142 : QI.subset (HI (142/32)) (hTab.getD 142 (QI.pt 0)) = true := by decide +kernel
theorem hCheck143 : QI.subset (HI (143/32)) (hTab.getD 143 (QI.pt 0)) = true := by decide +kernel
theorem hCheck144 : QI.subset (HI (144/32)) (hTab.getD 144 (QI.pt 0)) = true := by decide +kernel
theorem hCheck145 : QI.subset (HI (145/32)) (hTab.getD 145 (QI.pt 0)) = true := by decide +kernel
theorem hCheck146 : QI.subset (HI (146/32)) (hTab.getD 146 (QI.pt 0)) = true := by decide +kernel
theorem hCheck147 : QI.subset (HI (147/32)) (hTab.getD 147 (QI.pt 0)) = true := by decide +kernel
theorem hCheck148 : QI.subset (HI (148/32)) (hTab.getD 148 (QI.pt 0)) = true := by decide +kernel
theorem hCheck149 : QI.subset (HI (149/32)) (hTab.getD 149 (QI.pt 0)) = true := by decide +kernel
theorem hCheck150 : QI.subset (HI (150/32)) (hTab.getD 150 (QI.pt 0)) = true := by decide +kernel
theorem hCheck151 : QI.subset (HI (151/32)) (hTab.getD 151 (QI.pt 0)) = true := by decide +kernel
theorem hCheck152 : QI.subset (HI (152/32)) (hTab.getD 152 (QI.pt 0)) = true := by decide +kernel
theorem hCheck153 : QI.subset (HI (153/32)) (hTab.getD 153 (QI.pt 0)) = true := by decide +kernel
theorem hCheck154 : QI.subset (HI (154/32)) (hTab.getD 154 (QI.pt 0)) = true := by decide +kernel
theorem hCheck155 : QI.subset (HI (155/32)) (hTab.getD 155 (QI.pt 0)) = true := by decide +kernel
theorem hCheck156 : QI.subset (HI (156/32)) (hTab.getD 156 (QI.pt 0)) = true := by decide +kernel
theorem hCheck157 : QI.subset (HI (157/32)) (hTab.getD 157 (QI.pt 0)) = true := by decide +kernel
theorem hCheck158 : QI.subset (HI (158/32)) (hTab.getD 158 (QI.pt 0)) = true := by decide +kernel
theorem hCheck159 : QI.subset (HI (159/32)) (hTab.getD 159 (QI.pt 0)) = true := by decide +kernel
theorem hCheck160 : QI.subset (HI (160/32)) (hTab.getD 160 (QI.pt 0)) = true := by decide +kernel
theorem hCheck161 : QI.subset (HI (161/32)) (hTab.getD 161 (QI.pt 0)) = true := by decide +kernel
theorem hCheck162 : QI.subset (HI (162/32)) (hTab.getD 162 (QI.pt 0)) = true := by decide +kernel
theorem hCheck163 : QI.subset (HI (163/32)) (hTab.getD 163 (QI.pt 0)) = true := by decide +kernel
theorem hCheck164 : QI.subset (HI (164/32)) (hTab.getD 164 (QI.pt 0)) = true := by decide +kernel
theorem hCheck165 : QI.subset (HI (165/32)) (hTab.getD 165 (QI.pt 0)) = true := by decide +kernel
theorem hCheck166 : QI.subset (HI (166/32)) (hTab.getD 166 (QI.pt 0)) = true := by decide +kernel
theorem hCheck167 : QI.subset (HI (167/32)) (hTab.getD 167 (QI.pt 0)) = true := by decide +kernel
theorem hCheck168 : QI.subset (HI (168/32)) (hTab.getD 168 (QI.pt 0)) = true := by decide +kernel
theorem hCheck169 : QI.subset (HI (169/32)) (hTab.getD 169 (QI.pt 0)) = true := by decide +kernel
theorem hCheck170 : QI.subset (HI (170/32)) (hTab.getD 170 (QI.pt 0)) = true := by decide +kernel
theorem hCheck171 : QI.subset (HI (171/32)) (hTab.getD 171 (QI.pt 0)) = true := by decide +kernel
theorem hCheck172 : QI.subset (HI (172/32)) (hTab.getD 172 (QI.pt 0)) = true := by decide +kernel
theorem hCheck173 : QI.subset (HI (173/32)) (hTab.getD 173 (QI.pt 0)) = true := by decide +kernel
theorem hCheck174 : QI.subset (HI (174/32)) (hTab.getD 174 (QI.pt 0)) = true := by decide +kernel
theorem hCheck175 : QI.subset (HI (175/32)) (hTab.getD 175 (QI.pt 0)) = true := by decide +kernel
theorem hCheck176 : QI.subset (HI (176/32)) (hTab.getD 176 (QI.pt 0)) = true := by decide +kernel
theorem hCheck177 : QI.subset (HI (177/32)) (hTab.getD 177 (QI.pt 0)) = true := by decide +kernel
theorem hCheck178 : QI.subset (HI (178/32)) (hTab.getD 178 (QI.pt 0)) = true := by decide +kernel
theorem hCheck179 : QI.subset (HI (179/32)) (hTab.getD 179 (QI.pt 0)) = true := by decide +kernel
theorem hCheck180 : QI.subset (HI (180/32)) (hTab.getD 180 (QI.pt 0)) = true := by decide +kernel
theorem hCheck181 : QI.subset (HI (181/32)) (hTab.getD 181 (QI.pt 0)) = true := by decide +kernel
theorem hCheck182 : QI.subset (HI (182/32)) (hTab.getD 182 (QI.pt 0)) = true := by decide +kernel
theorem hCheck183 : QI.subset (HI (183/32)) (hTab.getD 183 (QI.pt 0)) = true := by decide +kernel
theorem hCheck184 : QI.subset (HI (184/32)) (hTab.getD 184 (QI.pt 0)) = true := by decide +kernel
theorem hCheck185 : QI.subset (HI (185/32)) (hTab.getD 185 (QI.pt 0)) = true := by decide +kernel
theorem hCheck186 : QI.subset (HI (186/32)) (hTab.getD 186 (QI.pt 0)) = true := by decide +kernel
theorem hCheck187 : QI.subset (HI (187/32)) (hTab.getD 187 (QI.pt 0)) = true := by decide +kernel
theorem hCheck188 : QI.subset (HI (188/32)) (hTab.getD 188 (QI.pt 0)) = true := by decide +kernel
theorem hCheck189 : QI.subset (HI (189/32)) (hTab.getD 189 (QI.pt 0)) = true := by decide +kernel
theorem hCheck190 : QI.subset (HI (190/32)) (hTab.getD 190 (QI.pt 0)) = true := by decide +kernel
theorem hCheck191 : QI.subset (HI (191/32)) (hTab.getD 191 (QI.pt 0)) = true := by decide +kernel
theorem hCheck192 : QI.subset (HI (192/32)) (hTab.getD 192 (QI.pt 0)) = true := by decide +kernel
theorem hCheck193 : QI.subset (HI (193/32)) (hTab.getD 193 (QI.pt 0)) = true := by decide +kernel
theorem hCheck194 : QI.subset (HI (194/32)) (hTab.getD 194 (QI.pt 0)) = true := by decide +kernel
theorem hCheck195 : QI.subset (HI (195/32)) (hTab.getD 195 (QI.pt 0)) = true := by decide +kernel
theorem hCheck196 : QI.subset (HI (196/32)) (hTab.getD 196 (QI.pt 0)) = true := by decide +kernel
theorem hCheck197 : QI.subset (HI (197/32)) (hTab.getD 197 (QI.pt 0)) = true := by decide +kernel
theorem hCheck198 : QI.subset (HI (198/32)) (hTab.getD 198 (QI.pt 0)) = true := by decide +kernel
theorem hCheck199 : QI.subset (HI (199/32)) (hTab.getD 199 (QI.pt 0)) = true := by decide +kernel
theorem hCheck200 : QI.subset (HI (200/32)) (hTab.getD 200 (QI.pt 0)) = true := by decide +kernel
theorem hCheck201 : QI.subset (HI (201/32)) (hTab.getD 201 (QI.pt 0)) = true := by decide +kernel
theorem hCheck202 : QI.subset (HI (202/32)) (hTab.getD 202 (QI.pt 0)) = true := by decide +kernel
theorem hCheck203 : QI.subset (HI (203/32)) (hTab.getD 203 (QI.pt 0)) = true := by decide +kernel
theorem hCheck204 : QI.subset (HI (204/32)) (hTab.getD 204 (QI.pt 0)) = true := by decide +kernel
theorem hCheck205 : QI.subset (HI (205/32)) (hTab.getD 205 (QI.pt 0)) = true := by decide +kernel
theorem hCheck206 : QI.subset (HI (206/32)) (hTab.getD 206 (QI.pt 0)) = true := by decide +kernel
theorem hCheck207 : QI.subset (HI (207/32)) (hTab.getD 207 (QI.pt 0)) = true := by decide +kernel
theorem hCheck208 : QI.subset (HI (208/32)) (hTab.getD 208 (QI.pt 0)) = true := by decide +kernel
theorem hCheck209 : QI.subset (HI (209/32)) (hTab.getD 209 (QI.pt 0)) = true := by decide +kernel
theorem hCheck210 : QI.subset (HI (210/32)) (hTab.getD 210 (QI.pt 0)) = true := by decide +kernel
theorem hCheck211 : QI.subset (HI (211/32)) (hTab.getD 211 (QI.pt 0)) = true := by decide +kernel
theorem hCheck212 : QI.subset (HI (212/32)) (hTab.getD 212 (QI.pt 0)) = true := by decide +kernel
theorem hCheck213 : QI.subset (HI (213/32)) (hTab.getD 213 (QI.pt 0)) = true := by decide +kernel
theorem hCheck214 : QI.subset (HI (214/32)) (hTab.getD 214 (QI.pt 0)) = true := by decide +kernel
theorem hCheck215 : QI.subset (HI (215/32)) (hTab.getD 215 (QI.pt 0)) = true := by decide +kernel
theorem hCheck216 : QI.subset (HI (216/32)) (hTab.getD 216 (QI.pt 0)) = true := by decide +kernel

theorem hTab_check (k : ℕ) (hk : k < 217) : QI.subset (HI ((k : ℚ)/32)) (hTab.getD k (QI.pt 0)) = true := by
  interval_cases k
  · exact hCheck0
  · exact hCheck1
  · exact hCheck2
  · exact hCheck3
  · exact hCheck4
  · exact hCheck5
  · exact hCheck6
  · exact hCheck7
  · exact hCheck8
  · exact hCheck9
  · exact hCheck10
  · exact hCheck11
  · exact hCheck12
  · exact hCheck13
  · exact hCheck14
  · exact hCheck15
  · exact hCheck16
  · exact hCheck17
  · exact hCheck18
  · exact hCheck19
  · exact hCheck20
  · exact hCheck21
  · exact hCheck22
  · exact hCheck23
  · exact hCheck24
  · exact hCheck25
  · exact hCheck26
  · exact hCheck27
  · exact hCheck28
  · exact hCheck29
  · exact hCheck30
  · exact hCheck31
  · exact hCheck32
  · exact hCheck33
  · exact hCheck34
  · exact hCheck35
  · exact hCheck36
  · exact hCheck37
  · exact hCheck38
  · exact hCheck39
  · exact hCheck40
  · exact hCheck41
  · exact hCheck42
  · exact hCheck43
  · exact hCheck44
  · exact hCheck45
  · exact hCheck46
  · exact hCheck47
  · exact hCheck48
  · exact hCheck49
  · exact hCheck50
  · exact hCheck51
  · exact hCheck52
  · exact hCheck53
  · exact hCheck54
  · exact hCheck55
  · exact hCheck56
  · exact hCheck57
  · exact hCheck58
  · exact hCheck59
  · exact hCheck60
  · exact hCheck61
  · exact hCheck62
  · exact hCheck63
  · exact hCheck64
  · exact hCheck65
  · exact hCheck66
  · exact hCheck67
  · exact hCheck68
  · exact hCheck69
  · exact hCheck70
  · exact hCheck71
  · exact hCheck72
  · exact hCheck73
  · exact hCheck74
  · exact hCheck75
  · exact hCheck76
  · exact hCheck77
  · exact hCheck78
  · exact hCheck79
  · exact hCheck80
  · exact hCheck81
  · exact hCheck82
  · exact hCheck83
  · exact hCheck84
  · exact hCheck85
  · exact hCheck86
  · exact hCheck87
  · exact hCheck88
  · exact hCheck89
  · exact hCheck90
  · exact hCheck91
  · exact hCheck92
  · exact hCheck93
  · exact hCheck94
  · exact hCheck95
  · exact hCheck96
  · exact hCheck97
  · exact hCheck98
  · exact hCheck99
  · exact hCheck100
  · exact hCheck101
  · exact hCheck102
  · exact hCheck103
  · exact hCheck104
  · exact hCheck105
  · exact hCheck106
  · exact hCheck107
  · exact hCheck108
  · exact hCheck109
  · exact hCheck110
  · exact hCheck111
  · exact hCheck112
  · exact hCheck113
  · exact hCheck114
  · exact hCheck115
  · exact hCheck116
  · exact hCheck117
  · exact hCheck118
  · exact hCheck119
  · exact hCheck120
  · exact hCheck121
  · exact hCheck122
  · exact hCheck123
  · exact hCheck124
  · exact hCheck125
  · exact hCheck126
  · exact hCheck127
  · exact hCheck128
  · exact hCheck129
  · exact hCheck130
  · exact hCheck131
  · exact hCheck132
  · exact hCheck133
  · exact hCheck134
  · exact hCheck135
  · exact hCheck136
  · exact hCheck137
  · exact hCheck138
  · exact hCheck139
  · exact hCheck140
  · exact hCheck141
  · exact hCheck142
  · exact hCheck143
  · exact hCheck144
  · exact hCheck145
  · exact hCheck146
  · exact hCheck147
  · exact hCheck148
  · exact hCheck149
  · exact hCheck150
  · exact hCheck151
  · exact hCheck152
  · exact hCheck153
  · exact hCheck154
  · exact hCheck155
  · exact hCheck156
  · exact hCheck157
  · exact hCheck158
  · exact hCheck159
  · exact hCheck160
  · exact hCheck161
  · exact hCheck162
  · exact hCheck163
  · exact hCheck164
  · exact hCheck165
  · exact hCheck166
  · exact hCheck167
  · exact hCheck168
  · exact hCheck169
  · exact hCheck170
  · exact hCheck171
  · exact hCheck172
  · exact hCheck173
  · exact hCheck174
  · exact hCheck175
  · exact hCheck176
  · exact hCheck177
  · exact hCheck178
  · exact hCheck179
  · exact hCheck180
  · exact hCheck181
  · exact hCheck182
  · exact hCheck183
  · exact hCheck184
  · exact hCheck185
  · exact hCheck186
  · exact hCheck187
  · exact hCheck188
  · exact hCheck189
  · exact hCheck190
  · exact hCheck191
  · exact hCheck192
  · exact hCheck193
  · exact hCheck194
  · exact hCheck195
  · exact hCheck196
  · exact hCheck197
  · exact hCheck198
  · exact hCheck199
  · exact hCheck200
  · exact hCheck201
  · exact hCheck202
  · exact hCheck203
  · exact hCheck204
  · exact hCheck205
  · exact hCheck206
  · exact hCheck207
  · exact hCheck208
  · exact hCheck209
  · exact hCheck210
  · exact hCheck211
  · exact hCheck212
  · exact hCheck213
  · exact hCheck214
  · exact hCheck215
  · exact hCheck216


def meshH (k : ℤ) : QI :=
  if k.natAbs < 217 then hTab.getD k.natAbs (QI.pt 0) else HI ((k : ℚ)/32)

theorem secondPrimitive_neg (x : ℝ) : secondPrimitive (-x) = secondPrimitive x := by
  simp [secondPrimitive, abs_neg]

theorem meshH_sound (k : ℤ) : (meshH k).Contains (secondPrimitive ((k : ℝ)/32)) := by
  unfold meshH
  split_ifs with hk
  · have h := QI.mem_of_subset (hTab_check k.natAbs hk) (HI_sound ((k.natAbs : ℚ)/32))
    have he : secondPrimitive ((k.natAbs : ℝ)/32) = secondPrimitive ((k : ℝ)/32) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
      simp [secondPrimitive, div_pow, sq_abs, abs_div, abs_abs]
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat, he] using h
  · simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat] using HI_sound ((k : ℚ)/32)

end Li2Lean.P0.ConfigRectangleBounds
