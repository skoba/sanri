import Sanri.History
import Sanri.SpecimenJudgment

namespace Sanri.MedicalFee.D006Genetic

open Sanri.Logic Sanri.History

private def primary (location : String) : SourceRef :=
  ⟨.primaryText, "令和8年厚生労働省告示第69号・別表第一", "令和8年度",
    "PDF177頁 " ++ location, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001686842.pdf"⟩

private def notice (location : String) : SourceRef :=
  ⟨.notification, "保医発0305第6号・別添1", "2026-10-07訂正後",
    location, .checkedAgainstSource,
    some "https://www.mhlw.go.jp/content/12400000/001757385.pdf"⟩

inductive Item where
  | simple | complex | veryComplex
  deriving DecidableEq, Repr

def ledgerItems : List Item := [.simple, .complex, .veryComplex]

def Item.number : Item → Nat
  | .simple => 1
  | .complex => 2
  | .veryComplex => 3

def ItemAt (n : Nat) (i : Item) : Prop := i.number = n

theorem modeled_number (i : Item) : 1 ≤ i.number ∧ i.number ≤ 3 := by
  cases i <;> decide

def Item.points : Item → Nat
  | .simple => 3880
  | .complex => 5000
  | .veryComplex => 8000

inductive Branch where
  | a | i | u | e | o
  deriving DecidableEq

/-- 通知(1)の枝と丸数字。旧入力と疾患識別子からの射影で共用する。 -/
structure DiseaseGroup where
  branch : Branch
  grade : Item

/-- 通知(1)に列挙された名称の識別子。括弧内の範囲指定も保持する。 -/
inductive Disease where
  | «デュシェンヌ型筋ジストロフィー»
  | «ベッカー型筋ジストロフィー»
  | «全身性アミロイドーシス»
  | «福山型先天性筋ジストロフィー»
  | «脊髄性筋萎縮症»
  | «栄養障害型表皮水疱症»
  | «先天性ＱＴ延長症候群»
  | «球脊髄性筋萎縮症»
  | «ハンチントン病»
  | «網膜芽細胞腫»
  | «甲状腺髄様癌»
  | «多発性内分泌腫瘍症１型»
  | «筋強直性ジストロフィー»
  | «先天性難聴»
  | «フェニルケトン尿症»
  | «ホモシスチン尿症»
  | «シトルリン血症（１型）»
  | «アルギノコハク酸血症»
  | «イソ吉草酸血症»
  | «ＨＭＧ血症»
  | «複合カルボキシラーゼ欠損症»
  | «グルタル酸血症１型»
  | «ＭＣＡＤ欠損症»
  | «ＶＬＣＡＤ欠損症»
  | «ＣＰＴ１欠損症»
  | «隆起性皮膚線維肉腫»
  | «先天性銅代謝異常症»
  | «メープルシロップ尿症»
  | «メチルマロン酸血症»
  | «プロピオン酸血症»
  | «メチルクロトニルグリシン尿症»
  | «ＭＴＰ（ＬＣＨＡＤ）欠損症»
  | «色素性乾皮症»
  | «家族性大動脈瘤・解離»
  | «ライソゾーム病（ムコ多糖症Ⅰ型、ムコ多糖症Ⅱ型、ゴーシェ病、ファブリ病及びポンペ病を含む。）»
  | «脆弱Ｘ症候群»
  | «レット症候群»
  | «ロウ症候群»
  | «三好型ミオパチー»
  | «レシチンコレステロールアシルトランスフェラーゼ欠損症»
  | «シトステロール血症»
  | «偽性副甲状腺機能低下症»
  | «プリオン病»
  | «クリオピリン関連周期熱症候群»
  | «脳内鉄沈着神経変性症»
  | «先天性大脳白質形成不全症（中枢神経白質形成異常症を含む。）»
  | «環状20番染色体症候群»
  | «ＰＣＤＨ19関連症候群»
  | «低ホスファターゼ症»
  | «ウィリアムズ症候群»
  | «アペール症候群»
  | «ロスムンド・トムソン症候群»
  | «プラダー・ウィリ症候群»
  | «１ｐ36欠失症候群»
  | «４ｐ欠失症候群»
  | «５ｐ欠失症候群»
  | «第14番染色体父親性ダイソミー症候群»
  | «アンジェルマン症候群»
  | «スミス・マギニス症候群»
  | «22ｑ11.2欠失症候群»
  | «エマヌエル症候群»
  | «脆弱Ｘ症候群関連疾患»
  | «ウォルフラム症候群»
  | «高ＩｇＤ症候群»
  | «化膿性無菌性関節炎・壊疽性膿皮症・アクネ症候群»
  | «先天異常症候群»
  | «副腎皮質刺激ホルモン不応症»
  | «根性点状軟骨異形成症１型»
  | «家族性部分性脂肪萎縮症»
  | «肺胞低換気症候群»
  | «脳腱黄色腫症»
  | «神経有棘赤血球症»
  | «先天性筋無力症候群»
  | «原発性免疫不全症候群»
  | «ペリー病»
  | «クルーゾン症候群»
  | «ファイファー症候群»
  | «アントレー・ビクスラー症候群»
  | «タンジール病»
  | «先天性赤血球形成異常性貧血»
  | «若年発症型両側性感音難聴»
  | «尿素サイクル異常症»
  | «マルファン症候群／ロイス・ディーツ症候群»
  | «血管型エーラスダンロス症候群»
  | «遺伝性自己炎症疾患»
  | «エプスタイン症候群»
  | «遺伝性ジストニア»
  | «先天性魚鱗癬»
  | «眼皮膚白皮症»
  | «乳児発症ＳＴＩＮＧ関連血管炎»
  | «進行性白質脳症»
  | «シャルコー・マリー・トゥース病»
  | «ＴＮＦ受容体関連周期性症候群»
  | «中條－西村症候群»
  | «家族性地中海熱»
  | «ベスレムミオパチー»
  | «過剰自己貪食を伴うＸ連鎖性ミオパチー»
  | «非ジストロフィー性ミオトニー症候群»
  | «遺伝性周期性四肢麻痺»
  | «ＨＴＲＡ１関連脳小血管病»
  | «結節性硬化症»
  | «肥厚性皮膚骨膜症»
  | «神経線維腫症»
  | «アレキサンダー病»
  | «非特異性多発性小腸潰瘍症»
  | «ＴＲＰＶ４異常症»
  | «マリネスコ・シェーグレン症候群»
  | «ガラクトース―１―リン酸ウリジルトランスフェラーゼ欠損症»
  | «進行性骨化性線維異形成症»
  | «無虹彩症»
  | «ＰＵＲＡ関連神経発達異常症»
  | «レーベル遺伝性視神経症»
  | «ソトス症候群»
  | «ＣＰＴ２欠損症»
  | «ＣＡＣＴ欠損症»
  | «ＯＣＴＮ－２異常症»
  | «シトリン欠損症»
  | «非ケトーシス型高グリシン血症»
  | «β－ケトチオラーゼ欠損症»
  | «メチルグルタコン酸尿症»
  | «グルタル酸血症２型»
  | «先天性副腎低形成症»
  | «ＡＴＲ－Ｘ症候群»
  | «ハッチンソン・ギルフォード症候群»
  | «軟骨無形成症»
  | «ウンフェルリヒト・ルンドボルグ病»
  | «ラフォラ病»
  | «セピアプテリン還元酵素欠損症»
  | «芳香族Ｌ－アミノ酸脱炭酸酵素欠損症»
  | «オスラー病»
  | «ＣＦＣ症候群»
  | «コステロ症候群»
  | «チャージ症候群»
  | «リジン尿性蛋白不耐症»
  | «副腎白質ジストロフィー»
  | «ブラウ症候群»
  | «鰓耳腎症候群»
  | «ヤング・シンプソン症候群»
  | «先天性腎性尿崩症»
  | «ビタミンＤ依存性くる病／骨軟化症»
  | «ネイルパテラ症候群（爪膝蓋症候群）／ＬＭＸ１Ｂ関連腎症»
  | «グルコーストランスポーター１欠損症»
  | «甲状腺ホルモン不応症»
  | «ウィーバー症候群»
  | «コフィン・ローリー症候群»
  | «モワット・ウィルソン症候群»
  | «肝型糖原病（糖原病Ⅰ型、Ⅲ型、Ⅵ型、Ⅸa型、Ⅸb型、Ⅸc型、Ⅳ型）»
  | «筋型糖原病（糖原病Ⅲ型、Ⅳ型、Ⅸd型）»
  | «先天性プロテインＣ欠乏症»
  | «先天性プロテインＳ欠乏症»
  | «先天性アンチトロンビン欠乏症»
  | «筋萎縮性側索硬化症»
  | «家族性特発性基底核石灰化症»
  | «縁取り空胞を伴う遠位型ミオパチー»
  | «シュワルツ・ヤンペル症候群»
  | «肥大型心筋症»
  | «家族性高コレステロール血症（ホモ接合体）»
  | «先天性ミオパチー»
  | «皮質下梗塞と白質脳症を伴う常染色体優性脳動脈症»
  | «神経軸索スフェロイド形成を伴う遺伝性びまん性白質脳症»
  | «先天性無痛無汗症»
  | «家族性良性慢性天疱瘡»
  | «那須・ハコラ病»
  | «カーニー複合»
  | «ペルオキシソーム形成異常症»
  | «ペルオキシソームβ酸化系酵素欠損症»
  | «プラスマローゲン合成酵素欠損症»
  | «アカタラセミア»
  | «原発性高シュウ酸尿症Ⅰ型»
  | «レフサム病»
  | «先天性葉酸吸収不全症»
  | «異型ポルフィリン症»
  | «先天性骨髄性ポルフィリン症»
  | «急性間欠性ポルフィリン症»
  | «赤芽球性プロトポルフィリン症»
  | «Ｘ連鎖優性プロトポルフィリン症»
  | «遺伝性コプロポルフィリン症»
  | «晩発性皮膚ポルフィリン症»
  | «肝性骨髄性ポルフィリン症»
  | «原発性高カイロミクロン血症»
  | «無βリポタンパク血症»
  | «タナトフォリック骨異形成症»
  | «遺伝性膵炎»
  | «嚢胞性線維症»
  | «アッシャー症候群（タイプ１、タイプ２、タイプ３）»
  | «カナバン病»
  | «先天性グリコシルホスファチジルイノシトール欠損症»
  | «大理石骨病»
  | «脳クレアチン欠乏症候群»
  | «ネフロン癆»
  | «家族性低βリポタンパク血症１（ホモ接合体）»
  | «進行性家族性肝内胆汁うっ滞症»
  | «ジュベール症候群関連疾患»
  | «ウェルナー症候群»
  | «コケイン症候群»
  | «弾性線維性仮性黄色腫»
  | «ダイアモンド・ブラックファン貧血»
  | «ＬＭＮＢ１関連大脳白質脳症»
  | «ドラベ症候群»
  | «コフィン・シリス症候群»
  | «歌舞伎症候群»
  | «肺胞蛋白症（自己免疫性又は先天性）»
  | «ヌーナン症候群»
  | «骨形成不全症»
  | «脊髄小脳変性症（多系統萎縮症を除く）»
  | «古典型エーラスダンロス症候群»
  | «非典型溶血性尿毒症症候群»
  | «アルポート症候群»
  | «ファンコニ貧血»
  | «遺伝性鉄芽球性貧血»
  | «アラジール症候群»
  | «ルビンシュタイン・テイビ症候群»
  | «ミトコンドリア病»
  | «線毛機能不全症候群（カルタゲナー症候群を含む。）»
  | «先天性副腎皮質酵素欠損症»
  | «出血性線溶異常症»
  deriving DecidableEq

def Disease.group : Disease → DiseaseGroup

  | .«デュシェンヌ型筋ジストロフィー»
  | .«ベッカー型筋ジストロフィー»
  | .«全身性アミロイドーシス» => ⟨.a, .simple⟩

  | .«福山型先天性筋ジストロフィー»
  | .«脊髄性筋萎縮症» => ⟨.a, .complex⟩

  | .«栄養障害型表皮水疱症»
  | .«先天性ＱＴ延長症候群» => ⟨.a, .veryComplex⟩

  | .«球脊髄性筋萎縮症» => ⟨.i, .simple⟩

  | .«ハンチントン病»
  | .«網膜芽細胞腫»
  | .«甲状腺髄様癌»
  | .«多発性内分泌腫瘍症１型» => ⟨.i, .complex⟩

  | .«筋強直性ジストロフィー»
  | .«先天性難聴» => ⟨.u, .simple⟩

  | .«フェニルケトン尿症»
  | .«ホモシスチン尿症»
  | .«シトルリン血症（１型）»
  | .«アルギノコハク酸血症»
  | .«イソ吉草酸血症»
  | .«ＨＭＧ血症»
  | .«複合カルボキシラーゼ欠損症»
  | .«グルタル酸血症１型»
  | .«ＭＣＡＤ欠損症»
  | .«ＶＬＣＡＤ欠損症»
  | .«ＣＰＴ１欠損症»
  | .«隆起性皮膚線維肉腫»
  | .«先天性銅代謝異常症» => ⟨.u, .complex⟩

  | .«メープルシロップ尿症»
  | .«メチルマロン酸血症»
  | .«プロピオン酸血症»
  | .«メチルクロトニルグリシン尿症»
  | .«ＭＴＰ（ＬＣＨＡＤ）欠損症»
  | .«色素性乾皮症»
  | .«家族性大動脈瘤・解離» => ⟨.u, .veryComplex⟩

  | .«ライソゾーム病（ムコ多糖症Ⅰ型、ムコ多糖症Ⅱ型、ゴーシェ病、ファブリ病及びポンペ病を含む。）»
  | .«脆弱Ｘ症候群»
  | .«レット症候群»
  | .«ロウ症候群»
  | .«三好型ミオパチー»
  | .«レシチンコレステロールアシルトランスフェラーゼ欠損症»
  | .«シトステロール血症»
  | .«偽性副甲状腺機能低下症» => ⟨.e, .simple⟩

  | .«プリオン病»
  | .«クリオピリン関連周期熱症候群»
  | .«脳内鉄沈着神経変性症»
  | .«先天性大脳白質形成不全症（中枢神経白質形成異常症を含む。）»
  | .«環状20番染色体症候群»
  | .«ＰＣＤＨ19関連症候群»
  | .«低ホスファターゼ症»
  | .«ウィリアムズ症候群»
  | .«アペール症候群»
  | .«ロスムンド・トムソン症候群»
  | .«プラダー・ウィリ症候群»
  | .«１ｐ36欠失症候群»
  | .«４ｐ欠失症候群»
  | .«５ｐ欠失症候群»
  | .«第14番染色体父親性ダイソミー症候群»
  | .«アンジェルマン症候群»
  | .«スミス・マギニス症候群»
  | .«22ｑ11.2欠失症候群»
  | .«エマヌエル症候群»
  | .«脆弱Ｘ症候群関連疾患»
  | .«ウォルフラム症候群»
  | .«高ＩｇＤ症候群»
  | .«化膿性無菌性関節炎・壊疽性膿皮症・アクネ症候群»
  | .«先天異常症候群»
  | .«副腎皮質刺激ホルモン不応症»
  | .«根性点状軟骨異形成症１型»
  | .«家族性部分性脂肪萎縮症»
  | .«肺胞低換気症候群»
  | .«脳腱黄色腫症» => ⟨.e, .complex⟩

  | .«神経有棘赤血球症»
  | .«先天性筋無力症候群»
  | .«原発性免疫不全症候群»
  | .«ペリー病»
  | .«クルーゾン症候群»
  | .«ファイファー症候群»
  | .«アントレー・ビクスラー症候群»
  | .«タンジール病»
  | .«先天性赤血球形成異常性貧血»
  | .«若年発症型両側性感音難聴»
  | .«尿素サイクル異常症»
  | .«マルファン症候群／ロイス・ディーツ症候群»
  | .«血管型エーラスダンロス症候群»
  | .«遺伝性自己炎症疾患»
  | .«エプスタイン症候群»
  | .«遺伝性ジストニア»
  | .«先天性魚鱗癬»
  | .«眼皮膚白皮症»
  | .«乳児発症ＳＴＩＮＧ関連血管炎»
  | .«進行性白質脳症»
  | .«シャルコー・マリー・トゥース病» => ⟨.e, .veryComplex⟩

  | .«ＴＮＦ受容体関連周期性症候群»
  | .«中條－西村症候群»
  | .«家族性地中海熱»
  | .«ベスレムミオパチー»
  | .«過剰自己貪食を伴うＸ連鎖性ミオパチー»
  | .«非ジストロフィー性ミオトニー症候群»
  | .«遺伝性周期性四肢麻痺»
  | .«ＨＴＲＡ１関連脳小血管病»
  | .«結節性硬化症»
  | .«肥厚性皮膚骨膜症»
  | .«神経線維腫症»
  | .«アレキサンダー病»
  | .«非特異性多発性小腸潰瘍症»
  | .«ＴＲＰＶ４異常症»
  | .«マリネスコ・シェーグレン症候群»
  | .«ガラクトース―１―リン酸ウリジルトランスフェラーゼ欠損症»
  | .«進行性骨化性線維異形成症»
  | .«無虹彩症»
  | .«ＰＵＲＡ関連神経発達異常症»
  | .«レーベル遺伝性視神経症» => ⟨.o, .simple⟩

  | .«ソトス症候群»
  | .«ＣＰＴ２欠損症»
  | .«ＣＡＣＴ欠損症»
  | .«ＯＣＴＮ－２異常症»
  | .«シトリン欠損症»
  | .«非ケトーシス型高グリシン血症»
  | .«β－ケトチオラーゼ欠損症»
  | .«メチルグルタコン酸尿症»
  | .«グルタル酸血症２型»
  | .«先天性副腎低形成症»
  | .«ＡＴＲ－Ｘ症候群»
  | .«ハッチンソン・ギルフォード症候群»
  | .«軟骨無形成症»
  | .«ウンフェルリヒト・ルンドボルグ病»
  | .«ラフォラ病»
  | .«セピアプテリン還元酵素欠損症»
  | .«芳香族Ｌ－アミノ酸脱炭酸酵素欠損症»
  | .«オスラー病»
  | .«ＣＦＣ症候群»
  | .«コステロ症候群»
  | .«チャージ症候群»
  | .«リジン尿性蛋白不耐症»
  | .«副腎白質ジストロフィー»
  | .«ブラウ症候群»
  | .«鰓耳腎症候群»
  | .«ヤング・シンプソン症候群»
  | .«先天性腎性尿崩症»
  | .«ビタミンＤ依存性くる病／骨軟化症»
  | .«ネイルパテラ症候群（爪膝蓋症候群）／ＬＭＸ１Ｂ関連腎症»
  | .«グルコーストランスポーター１欠損症»
  | .«甲状腺ホルモン不応症»
  | .«ウィーバー症候群»
  | .«コフィン・ローリー症候群»
  | .«モワット・ウィルソン症候群»
  | .«肝型糖原病（糖原病Ⅰ型、Ⅲ型、Ⅵ型、Ⅸa型、Ⅸb型、Ⅸc型、Ⅳ型）»
  | .«筋型糖原病（糖原病Ⅲ型、Ⅳ型、Ⅸd型）»
  | .«先天性プロテインＣ欠乏症»
  | .«先天性プロテインＳ欠乏症»
  | .«先天性アンチトロンビン欠乏症»
  | .«筋萎縮性側索硬化症»
  | .«家族性特発性基底核石灰化症»
  | .«縁取り空胞を伴う遠位型ミオパチー»
  | .«シュワルツ・ヤンペル症候群»
  | .«肥大型心筋症»
  | .«家族性高コレステロール血症（ホモ接合体）»
  | .«先天性ミオパチー»
  | .«皮質下梗塞と白質脳症を伴う常染色体優性脳動脈症»
  | .«神経軸索スフェロイド形成を伴う遺伝性びまん性白質脳症»
  | .«先天性無痛無汗症»
  | .«家族性良性慢性天疱瘡»
  | .«那須・ハコラ病»
  | .«カーニー複合»
  | .«ペルオキシソーム形成異常症»
  | .«ペルオキシソームβ酸化系酵素欠損症»
  | .«プラスマローゲン合成酵素欠損症»
  | .«アカタラセミア»
  | .«原発性高シュウ酸尿症Ⅰ型»
  | .«レフサム病»
  | .«先天性葉酸吸収不全症»
  | .«異型ポルフィリン症»
  | .«先天性骨髄性ポルフィリン症»
  | .«急性間欠性ポルフィリン症»
  | .«赤芽球性プロトポルフィリン症»
  | .«Ｘ連鎖優性プロトポルフィリン症»
  | .«遺伝性コプロポルフィリン症»
  | .«晩発性皮膚ポルフィリン症»
  | .«肝性骨髄性ポルフィリン症»
  | .«原発性高カイロミクロン血症»
  | .«無βリポタンパク血症»
  | .«タナトフォリック骨異形成症»
  | .«遺伝性膵炎»
  | .«嚢胞性線維症»
  | .«アッシャー症候群（タイプ１、タイプ２、タイプ３）»
  | .«カナバン病»
  | .«先天性グリコシルホスファチジルイノシトール欠損症»
  | .«大理石骨病»
  | .«脳クレアチン欠乏症候群»
  | .«ネフロン癆»
  | .«家族性低βリポタンパク血症１（ホモ接合体）»
  | .«進行性家族性肝内胆汁うっ滞症»
  | .«ジュベール症候群関連疾患»
  | .«ウェルナー症候群»
  | .«コケイン症候群»
  | .«弾性線維性仮性黄色腫»
  | .«ダイアモンド・ブラックファン貧血»
  | .«ＬＭＮＢ１関連大脳白質脳症» => ⟨.o, .complex⟩

  | .«ドラベ症候群»
  | .«コフィン・シリス症候群»
  | .«歌舞伎症候群»
  | .«肺胞蛋白症（自己免疫性又は先天性）»
  | .«ヌーナン症候群»
  | .«骨形成不全症»
  | .«脊髄小脳変性症（多系統萎縮症を除く）»
  | .«古典型エーラスダンロス症候群»
  | .«非典型溶血性尿毒症症候群»
  | .«アルポート症候群»
  | .«ファンコニ貧血»
  | .«遺伝性鉄芽球性貧血»
  | .«アラジール症候群»
  | .«ルビンシュタイン・テイビ症候群»
  | .«ミトコンドリア病»
  | .«線毛機能不全症候群（カルタゲナー症候群を含む。）»
  | .«先天性副腎皮質酵素欠損症»
  | .«出血性線溶異常症» => ⟨.o, .veryComplex⟩

def Disease.Belongs (d : Disease) (branch : Branch) (grade : Item) : Prop :=
  d.group.branch = branch ∧ d.group.grade = grade

theorem Disease.belongs_unique (d : Disease) :
    ∃ g : DiseaseGroup, d.Belongs g.branch g.grade ∧
      ∀ other : DiseaseGroup, d.Belongs other.branch other.grade → other = g := by
  refine ⟨d.group, ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨branch, grade⟩ ⟨hb, hg⟩
  cases h : d.group
  simp_all

example : Disease.«球脊髄性筋萎縮症».Belongs .i .simple := ⟨rfl, rfl⟩

example : ¬ Disease.«球脊髄性筋萎縮症».Belongs .i .veryComplex := by
  intro h
  cases h.2

inductive Method where
  | pcr | sequencing | fish | southernBlot | other
  deriving DecidableEq

structure Examination where
  performance : Performance Nat
  suspected : Option Bool := none
  group : Option DiseaseGroup := none
  method : Option Method := none
  undiagnosableByOtherMeans : Option Bool := none
  /-- 通知(1)の「２回以上」の起算と対象を確認した実施履歴の照会期間。 -/
  repeatPeriod : Option Period := none
  repeatNecessary : Option Bool := none

inductive Application where
  | single
  | multiple (others : List Examination)

structure Context where
  principal : Examination
  item : Item
  application : Application
  diseaseFacilityComplies : Option Bool := none
  diseaseFacilityNotified : Option Bool := none
  bundleFacilityComplies : Option Bool := none
  bundleFacilityNotified : Option Bool := none
  privacyGuidance : Option Bool := none
  geneticGuideline : Option Bool := none
  bundleGuideline : Option Bool := none
  bundleNecessary : Option Bool := none
  principalConfirmed : Option Bool := none
  priorPerformances : Option (Snapshot (Performance Nat)) := none

def Context.exams (c : Context) : List Examination :=
  c.principal :: (match c.application with
    | .single => []
    | .multiple others => others)

def priorCount (c : Context) (e : Examination) : Option Nat := do
  let h ← c.priorPerformances
  let period ← e.repeatPeriod
  let site := e.performance.site
  return (← h.select Performance.site ⟨site.patient, none, period⟩
    (fun p => p.item == e.performance.item)).length

def DiseaseFacility (c : Context) : Prop :=
  c.diseaseFacilityComplies = some true ∧ c.diseaseFacilityNotified = some true

def BranchCondition (c : Context) (branch : Branch) (e : Examination) : Prop :=
  match branch with
  | .a => ∃ m ∈ [Method.pcr, .sequencing, .fish, .southernBlot], e.method = some m
  | .i => e.method = some .pcr
  | .u => True
  | .e => DiseaseFacility c
  | .o => DiseaseFacility c ∧ e.undiagnosableByOtherMeans = some true

def RepeatCondition (c : Context) : Prop :=
  ∀ e ∈ c.exams, ∃ n, priorCount c e = some n ∧
    (n = 0 ∨ e.repeatNecessary = some true)

def Listed (c : Context) : Prop :=
  ∀ e ∈ c.exams, e.suspected = some true ∧
    ∃ g, e.group = some g ∧ (g.branch = .i → g.grade ≠ .veryComplex)

def DesignatedDiseaseFacility (c : Context) : Prop :=
  ∀ e ∈ c.exams, ∀ g, e.group = some g →
    g.branch = .e ∨ g.branch = .o → DiseaseFacility c

def BranchApplies (c : Context) (b : Branch) : Prop :=
  ∀ e ∈ c.exams, ∀ g, e.group = some g → g.branch = b → BranchCondition c b e

def Grade (c : Context) (i : Item) : Prop :=
  c.item = i → ∃ g, c.principal.group = some g ∧ g.grade = i

def BundleFacilityAndDraw (c : Context) : Prop :=
  match c.application with
  | .single => True
  | .multiple others =>
    c.bundleFacilityComplies = some true ∧ c.bundleFacilityNotified = some true ∧
    c.principalConfirmed = some true ∧ others ≠ [] ∧
    (c.exams.map (·.performance.item)).Nodup ∧
    ∀ e ∈ others, c.principal.performance.sameDraw e.performance = some true

def BundleIndication (c : Context) : Prop :=
  match c.application with
  | .single => True
  | .multiple _ => c.bundleGuideline = some true ∧ c.bundleNecessary = some true

inductive Entry where
  | repeatNecessity (disease : Nat)
  | cannotDiagnoseAndNecessity (disease : Nat)
  | bundledNamesAndNecessity (diseases : List Nat)

structure Result where
  base : Nat
  addition : Nat

def Result.total (r : Result) : Nat := r.base + r.addition

def simpleRule : Rule Context Result :=
  ⟨"primary/D006-4/item/1", primary "D006-4 1", fun c r =>
    c.item = .simple → r.base = 3880⟩

def complexRule : Rule Context Result :=
  ⟨"primary/D006-4/item/2", primary "D006-4 2", fun c r =>
    c.item = .complex → r.base = 5000⟩

def veryComplexRule : Rule Context Result :=
  ⟨"primary/D006-4/item/3", primary "D006-4 3", fun c r =>
    c.item = .veryComplex → r.base = 8000⟩

def facilityRule : Rule Context Result :=
  ⟨"primary/D006-4/note/1", primary "D006-4 注1", fun c _ =>
    DesignatedDiseaseFacility c⟩

def bundleRule : Rule Context Result :=
  ⟨"primary/D006-4/note/2", primary "D006-4 注2", fun c r =>
    BundleFacilityAndDraw c ∧ match c.application with
      | .single => r.addition = 0
      | .multiple _ => 2 * r.addition = r.base⟩

def frequencyRule : Rule Context Result :=
  ⟨"notice/D006-4/paragraph/1", notice "PDF341頁 D006-4(1)", fun c _ =>
    Listed c ∧ RepeatCondition c⟩

def aRule : Rule Context Result :=
  ⟨"notice/D006-4/paragraph/1/a", notice "PDF341頁 D006-4(1)ア",
    fun c _ => BranchApplies c .a⟩

def iRule : Rule Context Result :=
  ⟨"notice/D006-4/paragraph/1/i", notice "PDF341頁 D006-4(1)イ",
    fun c _ => BranchApplies c .i⟩

def uRule : Rule Context Result :=
  ⟨"notice/D006-4/paragraph/1/u", notice "PDF341頁 D006-4(1)ウ",
    fun c _ => BranchApplies c .u⟩

def eRule : Rule Context Result :=
  ⟨"notice/D006-4/paragraph/1/e", notice "PDF341–342頁 D006-4(1)エ",
    fun c _ => BranchApplies c .e⟩

def oRule : Rule Context Result :=
  ⟨"notice/D006-4/paragraph/1/o", notice "PDF342–343頁 D006-4(1)オ",
    fun c _ => BranchApplies c .o⟩

def guidanceRule : Rule Context Result :=
  ⟨"notice/D006-4/paragraph/2", notice "PDF343頁 D006-4(2)", fun c _ =>
    c.privacyGuidance = some true ∧ c.geneticGuideline = some true⟩

def diseaseFacilityRule : Rule Context Result :=
  ⟨"notice/D006-4/paragraph/3", notice "PDF343頁 D006-4(3)", fun c _ =>
    DesignatedDiseaseFacility c⟩

def simpleGradeRule : Rule Context Result :=
  ⟨"notice/D006-4/paragraph/5", notice "PDF343頁 D006-4(5)", fun c _ => Grade c .simple⟩

def complexGradeRule : Rule Context Result :=
  ⟨"notice/D006-4/paragraph/6", notice "PDF343頁 D006-4(6)", fun c _ => Grade c .complex⟩

def veryComplexGradeRule : Rule Context Result :=
  ⟨"notice/D006-4/paragraph/7", notice "PDF343頁 D006-4(7)", fun c _ => Grade c .veryComplex⟩

def bundleIndicationRule : Rule Context Result :=
  ⟨"notice/D006-4/paragraph/8", notice "PDF343–344頁 D006-4(8)",
    fun c _ => BundleIndication c⟩

/-- 摘要欄に要求する内容。実際に記載したかどうかは点数の前提と別に扱う。 -/
def repeatEntryRule : Rule Context (Entry → Prop) :=
  ⟨"notice/D006-4/paragraph/1", notice "PDF341頁 D006-4(1) 摘要", fun c entries =>
    ∀ e ∈ c.exams, ∀ n, priorCount c e = some n → 0 < n →
      entries (.repeatNecessity e.performance.item)⟩

def diagnosticEntryRule : Rule Context (Entry → Prop) :=
  ⟨"notice/D006-4/paragraph/4", notice "PDF343頁 D006-4(4)", fun c entries =>
    ∀ e ∈ c.exams, ∀ g, e.group = some g → g.branch = .o →
      entries (.cannotDiagnoseAndNecessity e.performance.item)⟩

def bundleEntryRule : Rule Context (Entry → Prop) :=
  ⟨"notice/D006-4/paragraph/8", notice "PDF343–344頁 D006-4(8) 摘要", fun c entries =>
    ∀ others, (∃ n, c.application = .multiple n ∧
      others = c.exams.map (·.performance.item)) → entries (.bundledNamesAndNecessity others)⟩

def rules := [simpleRule, complexRule, veryComplexRule, facilityRule, bundleRule,
  frequencyRule, aRule, iRule, uRule, eRule, oRule, guidanceRule, diseaseFacilityRule,
  simpleGradeRule, complexGradeRule, veryComplexGradeRule, bundleIndicationRule]

def Eligible (c : Context) : Prop :=
  DesignatedDiseaseFacility c ∧ BundleFacilityAndDraw c ∧ Listed c ∧ RepeatCondition c ∧
  BranchApplies c .a ∧ BranchApplies c .i ∧ BranchApplies c .u ∧
  BranchApplies c .e ∧ BranchApplies c .o ∧
  c.privacyGuidance = some true ∧ c.geneticGuideline = some true ∧
  Grade c .simple ∧ Grade c .complex ∧ Grade c .veryComplex ∧ BundleIndication c

def scheduled (c : Context) : Result :=
  ⟨c.item.points, match c.application with
    | .single => 0
    | .multiple _ => c.item.points / 2⟩

theorem satisfies_iff (c : Context) (r : Result) :
    Satisfies rules c r ↔ Eligible c ∧ r = scheduled c := by
  obtain ⟨base, addition⟩ := r
  simp only [rules, satisfies_cons, satisfies_nil, simpleRule, complexRule, veryComplexRule,
    facilityRule, bundleRule, frequencyRule, aRule, iRule, uRule, eRule, oRule, guidanceRule,
    diseaseFacilityRule, simpleGradeRule, complexGradeRule, veryComplexGradeRule,
    bundleIndicationRule, Eligible, scheduled, Result.mk.injEq, and_true]
  cases c.item <;> cases c.application <;>
    simp [Item.points, *] <;>
    (constructor <;> intro h <;> simp_all only [and_assoc] <;> grind)

theorem determines : DeterminesOn Eligible rules := by
  intro c h
  exact ⟨⟨scheduled c, (satisfies_iff _ _).mpr ⟨h, rfl⟩⟩,
    fun a b ha hb => ((satisfies_iff _ _).mp ha).2.trans ((satisfies_iff _ _).mp hb).2.symm⟩

def PermitsPoints (c : Context) (p : Nat) : Prop :=
  ∃ r, Satisfies rules c r ∧ r.total = p

theorem permits_points_iff (c : Context) (p : Nat) :
    PermitsPoints c p ↔ Eligible c ∧ (scheduled c).total = p := by
  constructor
  · rintro ⟨r, hr, hp⟩
    obtain ⟨eligible, rfl⟩ := (satisfies_iff _ _).mp hr
    exact ⟨eligible, hp⟩
  · rintro ⟨h, hp⟩
    exact ⟨scheduled c, (satisfies_iff _ _).mpr ⟨h, rfl⟩, hp⟩

/-- 履歴の疾患IDから通知の疾患識別子への照合は、元のIDを保持したまま行う。 -/
structure ClassifiedContext where
  assessment : Context
  identify : Nat → Option Disease

def ClassifiedContext.Matches (c : ClassifiedContext) : Prop :=
  ∀ e ∈ c.assessment.exams, ∃ d, c.identify e.performance.item = some d ∧
    e.group = some d.group

/-- 同定した疾患から、従来の実施入力に群・等級を設定する。 -/
def classify (c : Context) (identify : Nat → Option Disease) : Option ClassifiedContext := do
  let classifyExam (e : Examination) := do
    let disease ← identify e.performance.item
    return ({ e with group := some disease.group } : Examination)
  let principal ← classifyExam c.principal
  let group ← principal.group
  let application ← match c.application with
    | .single => some .single
    | .multiple others => (others.mapM classifyExam).map Application.multiple
  return ⟨{ c with principal, item := group.grade, application }, identify⟩

private def diseaseRule (id location : String) (branch : Branch) (grade : Item) :
    Rule ClassifiedContext Result :=
  ⟨"notice/D006-4/paragraph/1/" ++ id, notice location, fun c _ =>
    ∀ e ∈ c.assessment.exams, ∀ g, e.group = some g →
      g.branch = branch → g.grade = grade →
      ∃ d, c.identify e.performance.item = some d ∧ d.Belongs branch grade⟩

def diseaseA1Rule :=
  diseaseRule "a/1" "PDF341頁 D006-4(1)ア①" .a .simple

def diseaseA2Rule :=
  diseaseRule "a/2" "PDF341頁 D006-4(1)ア②" .a .complex

def diseaseA3Rule :=
  diseaseRule "a/3" "PDF341頁 D006-4(1)ア③" .a .veryComplex

def diseaseI1Rule :=
  diseaseRule "i/1" "PDF341頁 D006-4(1)イ①" .i .simple

def diseaseI2Rule :=
  diseaseRule "i/2" "PDF341頁 D006-4(1)イ②" .i .complex

def diseaseU1Rule :=
  diseaseRule "u/1" "PDF341頁 D006-4(1)ウ①" .u .simple

def diseaseU2Rule :=
  diseaseRule "u/2" "PDF341頁 D006-4(1)ウ②" .u .complex

def diseaseU3Rule :=
  diseaseRule "u/3" "PDF341頁 D006-4(1)ウ③" .u .veryComplex

def diseaseE1Rule :=
  diseaseRule "e/1" "PDF341頁 D006-4(1)エ①" .e .simple

def diseaseE2Rule :=
  diseaseRule "e/2" "PDF341–342頁 D006-4(1)エ②" .e .complex

def diseaseE3Rule :=
  diseaseRule "e/3" "PDF342頁 D006-4(1)エ③" .e .veryComplex

def diseaseO1Rule :=
  diseaseRule "o/1" "PDF342頁 D006-4(1)オ①" .o .simple

def diseaseO2Rule :=
  diseaseRule "o/2" "PDF342–343頁 D006-4(1)オ②" .o .complex

def diseaseO3Rule :=
  diseaseRule "o/3" "PDF343頁 D006-4(1)オ③" .o .veryComplex

def diseaseRules :=
  [diseaseA1Rule, diseaseA2Rule, diseaseA3Rule, diseaseI1Rule, diseaseI2Rule,
   diseaseU1Rule, diseaseU2Rule, diseaseU3Rule, diseaseE1Rule, diseaseE2Rule,
   diseaseE3Rule, diseaseO1Rule, diseaseO2Rule, diseaseO3Rule]

def classifiedRules : List (Rule ClassifiedContext Result) :=
  (rules.map fun rule => ⟨rule.id, rule.source, fun c r => rule.holds c.assessment r⟩) ++
    diseaseRules

theorem classified_determines (c : ClassifiedContext)
    (eligible : Eligible c.assessment) (identified : c.Matches) :
    DeterminesAt classifiedRules c := by
  have equivalence (r : Result) :
      Satisfies classifiedRules c r ↔ Satisfies rules c.assessment r := by
    constructor
    · intro h rule hr
      exact h _ (List.mem_append_left _ (List.mem_map.mpr ⟨rule, hr, rfl⟩))
    · intro h rule hr
      rcases List.mem_append.mp hr with lifted | listed
      · obtain ⟨original, ho, rfl⟩ := List.mem_map.mp lifted
        exact h original ho
      · have applies (id location : String) (branch : Branch) (grade : Item) :
            (diseaseRule id location branch grade).holds c r := by
          intro e he g hg hb hi
          obtain ⟨d, hd, hg'⟩ := identified e he
          have eq := Option.some.inj (hg'.symm.trans hg)
          exact ⟨d, hd, congrArg DiseaseGroup.branch eq |>.trans hb,
            congrArg DiseaseGroup.grade eq |>.trans hi⟩
        simp only [diseaseRules, List.mem_cons, List.not_mem_nil, or_false] at listed
        rcases listed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl <;> exact applies _ _ _ _
  obtain ⟨⟨r, hr⟩, unique⟩ := determines c.assessment eligible
  exact ⟨⟨r, (equivalence r).mpr hr⟩,
    fun a b ha hb => unique a b ((equivalence a).mp ha) ((equivalence b).mp hb)⟩

def judgmentTest (i : Item) : SpecimenJudgment.Test :=
  { major := 6, suffix := 4, number := i.number, ordinaryCategory := .hematological }

theorem judgment_category (i : Item) :
    SpecimenJudgment.categoryFor (judgmentTest i) = some .geneticChromosomal := rfl

private def exampleSite : Site := ⟨1, 1, ⟨⟨2026, 9⟩, ⟨21, by decide⟩⟩⟩

private def exampleExam : Examination :=
  { performance := ⟨1, exampleSite, 1, some 1, some 1, none, none⟩
    suspected := some true, group := some ⟨.a, .simple⟩, method := some .pcr
    repeatPeriod := some (Period.through exampleSite.date) }

private def exampleContext : Context :=
  { principal := exampleExam, item := .simple, application := .single
    privacyGuidance := some true, geneticGuideline := some true
    priorPerformances := some ⟨⟨1, none, Period.through exampleSite.date⟩, []⟩ }

private theorem example_eligible : Eligible exampleContext := by
  simp [Eligible, exampleContext, exampleExam, DesignatedDiseaseFacility, Context.exams,
    BundleFacilityAndDraw, Listed, RepeatCondition, BranchApplies, Grade, BundleIndication,
    priorCount, Snapshot.select, Scope.Covers, Period.Within, BranchCondition]
  all_goals first | rfl | exact ⟨.pcr, by simp, rfl⟩

example : Satisfies rules exampleContext ⟨3880, 0⟩ :=
  (satisfies_iff _ _).mpr ⟨example_eligible, rfl⟩

private def otherExam : Examination :=
  { exampleExam with
    performance := { exampleExam.performance with id := 2, item := 2 }
    group := some ⟨.i, .complex⟩ }

private def exampleBundle : Context :=
  { exampleContext with
    application := .multiple [otherExam], principalConfirmed := some true
    bundleFacilityComplies := some true, bundleFacilityNotified := some true
    bundleGuideline := some true, bundleNecessary := some true }

private theorem example_bundle_eligible : Eligible exampleBundle := by
  simp [Eligible, exampleBundle, exampleContext, exampleExam, otherExam,
    DesignatedDiseaseFacility, Context.exams, BundleFacilityAndDraw, Listed,
    RepeatCondition, BranchApplies, Grade, BundleIndication, priorCount, Snapshot.select,
    Scope.Covers, Period.Within, BranchCondition, Performance.sameDraw, Performance.sameGroup]
  all_goals first | rfl | exact ⟨.pcr, by simp, rfl⟩

example : PermitsPoints exampleBundle 5820 :=
  (permits_points_iff _ _).mpr ⟨example_bundle_eligible, rfl⟩

example : ¬ SatisfiableAt rules { exampleContext with priorPerformances := none } := by
  rintro ⟨r, hr⟩
  have h := (satisfies_iff _ _).mp hr |>.1.2.2.2.1
  have ⟨n, h, _⟩ := h exampleExam (by simp [Context.exams, exampleContext])
  contradiction

example : ¬ SatisfiableAt rules { exampleContext with geneticGuideline := some false } := by
  rintro ⟨r, hr⟩
  have h := (satisfies_iff _ _).mp hr
  simp [Eligible, exampleContext] at h

end Sanri.MedicalFee.D006Genetic
