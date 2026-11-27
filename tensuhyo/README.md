# 電子点数表の参照資料

[医科及び歯科電子点数表の配布ページ](https://www.hpdx.or.jp/seikyushiharai/tensuhyo/ikashika/index.html)から各利用者が取得した資料を、ローカルで保存・参照するためのフォルダです。公式資料とその変換・正規化・抜粋データはGit管理から除外し、GitHubには公開しません。このフォルダから公開するのは本READMEだけです。

リポジトリをcloneしても資料は含まれません。提供元の利用条件を確認の上、配布ページから対象版のZIP・手引きPDFを取得して配置してください。以下の保存先は、このREADMEからのローカル相対パスです。

## ローカル参照用に取得した版

| 資料 | 配布ページの公開日 | 保存先 |
| --- | --- | --- |
| 医科電子点数表テーブル・令和8年度版 | 2026-10-13 | `ika/2026-10-13/tensuhyo_02.zip` |
| 活用の手引き（医科） | 2026-07-24 | `ika/2026-10-13/tensuhyo_01.pdf` |
| ファイル一覧表（ZIP内の資料） | 上記ZIPに同梱 | `ika/2026-10-13/tables/00ファイル一覧表（医科）.pdf` |

取得日は2026-10-22です。ローカルの `ika/2026-10-13/sources.json` に取得元URL、取得日時、ファイルサイズ、SHA-256、CSVの行数・列数を記録しています。更新時には別の日付のフォルダに保存して、既存の版を残します。配布ページの資料は更新されるため、再取得時は対象の公開日・版を確認してください。

## 展開したテーブル

`ika/2026-10-13/tables/` のCSVは、検索・閲覧用に**CP932からUTF-8へ変換し、改行をLFに統一**しています。ヘッダーは追加せず、項目の順序・値は維持しています。配布時のバイト列は原本ZIPに残しています。日本語ファイル名もCP932として復元しています。

| ファイル | 行数 |
| --- | ---: |
| 01 補助マスターテーブル.csv | 11,835 |
| 02 包括テーブル.csv | 248,253 |
| 03-1 背反テーブル1.csv | 39,534 |
| 03-2 背反テーブル2.csv | 21,662 |
| 03-3 背反テーブル3.csv | 17,252 |
| 03-4 背反テーブル4.csv | 352 |
| 04 入院基本料テーブル.csv | 7,051 |
| 05 算定回数テーブル.csv | 6,350 |

リポジトリのルートから、名称や診療行為コードで検索できます。

```sh
rg -n -m 5 '検体検査判断料' 'tensuhyo/ika/2026-10-13/tables/01 補助マスターテーブル.csv'
rg -n '"111000110"' tensuhyo/ika/2026-10-13/tables
```

列の意味や背反テーブルの区分は手引きPDFを参照してください。これらは公式配布資料とその文字コード変換版であり、Sanri独自のLean定義とは区別して管理します。

点数等を持つ[診療行為マスター](https://www.hpdx.or.jp/seikyushiharai/tensuhyo/kihonmasta/index.html)は別配布です。取得と取込は[下記](#診療行為マスターを取り込む)のとおりです。また、CSVの有無だけで算定可否を判定せず、手引きの留意点と告示・通知の条件を併せて参照します。

取込・評価器の設計は [DESIGN.md](../DESIGN.md)、現CSVの列配置と解釈上の注意は [参照スキーマ](../docs/tensuhyo-schema.md)にまとめています。

## 本文・通知・疑義解釈のローカル資料

公式の参照先と確認範囲は [資料台帳](../docs/source-register.md)に記録しています。2026-10-22に次のPDFを `mhlw/r08/` へ取得し、URL・取得日時・SHA-256を同フォルダの `sources.json` に保存しました。これらもGit管理外です。

- `ika-primary.pdf`：医科点数表本文。資料台帳の本文PDF。
- `ika-notification-20261007.pdf`：医科留意事項、集約ページの1007訂正後。
- `clarification-01-20260323.pdf`：疑義解釈その1。

取得したPDF全体を確認済みという意味ではありません。疑義解釈の後続資料、訂正・廃止、各区分の対象期間を別に追跡します。

## 本文PDFからLean草案を作る

一度だけ、資料台帳の[別表第一・医科点数表PDF](https://www.mhlw.go.jp/content/12400000/001686842.pdf)を `tensuhyo/mhlw/r08/ika-primary.pdf` に置きます。リポジトリのルートで次を実行してください。Python 3.10以降、Popplerの `pdftotext`（Ubuntuの `poppler-utils` またはCUPS snap同梱版）、リポジトリ指定のLeanとLakeを使用します。

```sh
python3 -m tools.fee_inventory
python3 -m tools.notice_inventory
python3 -m tools.draft_fee D216-2
python3 -m tools.draft_fee A000 D007
```

取得日2026-10-22の登録版とPDFのSHA-256を照合し、物理ページ番号・抽出行番号付きで指定区分を取り出します。別の場所にある同じPDFには `--pdf パス` を指定できます。区分の開始と終端を特定できない場合はエラーになります。

通知索引がある場合は、登録版の通知PDFのSHA-256と頁数も検査してから通知を抽出します。

型検査が通ると、区分ごとに `tensuhyo/drafts/<区分番号>/<生成内容のハッシュ>/` が表示されます。

- `review.json` に、資料ID・版・URL・ハッシュ、該当頁、抽出した本文の各行と判定を記録します。`unresolved` は、原文に戻って書き起こす行です。表の折返しやルビは紙面上の位置も確認してください。
- `review.json` の `notice` に、通知の区分範囲・各段落の位置と該当行を記録します。索引に該当区分がなければ `not_found`、索引ファイルがなければ `index_missing` を記録します。併記見出しは共有範囲として表示します。
- `Draft.lean` には、定型に合う所定点数と区分全体に明記された患者単位の月上限の候補を、出典付きの制約として出力します。すべて未レビューの扱いです。複雑な区分では規則が0件でも、対応する本文を `review.json` で読めます。

次の実装依頼では「D007を本文から形式化」のように指定できます。レビュー時は区分外の通則、ただし書、通知・疑義解釈の適用を確認し、既存モデルとの対応と境界例を検証します。型検査の結果は生成したLeanの構文・型についての確認です。Lean草案の規則候補は本文から生成します。通知は個別の出典としてレビューし、疑義解釈は原資料を参照します。実データを含む草案とレビュー資料はこのフォルダ内に保存されます。

## 本文と通知の位置索引を再生成する

上記の登録版本文・通知PDFを配置し、リポジトリのルートで実行します。

```sh
lake build
python3 -m tools.fee_inventory
python3 -m tools.notice_inventory
python3 -m tools.specimen_backlog
git check-ignore tensuhyo/inventory/{fee-index,notice-index,notice-ledger-check,specimen-backlog}.json
```

出力先はGit管理外の `tensuhyo/inventory/` です。

- `fee-index.json` は本文の区分見出しと項・注の開始位置を持ちます。判定が難しい区分では、候補と問題を記録し、分母を未確定にします。
- `notice-index.json` は通知の区分・通則・段落の位置と抽出上の問題を持ちます。本文側だけ・通知側だけで見つかった区分も記録します。
- `notice-ledger-check.json` は公開Leanの通知参照について、位置が一意に見つかったID、見つからないID、候補が重複したIDを記録します。
- `specimen-backlog.json` は本文の第2章第3部第1節と第4節のD400台を対象に、工程3aで原文と照合する項・注・段落を記録します。公開Lean台帳のIDで対応を集計し、旧来の計算モデルだけにある規則は件数から除きます。索引で通知を特定できなかった区分の通知件数は未確定です。

位置情報はPopplerの物理頁・抽出行に対応します。番号の異常、対象外の資料、対応の判定単位は[索引の形式](../docs/tensuhyo-schema.md#本文・通知の位置索引)を参照してください。

## 全区分の残作業を見る

同じ登録版の本文PDFを使い、リポジトリのルートで実行します。

```sh
lake build
python3 -m tools.fee_inventory
python3 -m tools.fee_backlog
```

`inventory/fee-index.json` に出典・階層・見出しの位置、`inventory/medical-backlog.tsv` に枝番号ごとの既存実装と残作業を保存します。TSVはUTF-8のタブ区切りです。「種別＝区分」「既存実装との対応＝参照のみ」で、他区分から参照されていて個別料金が未実装の行を抽出できます。どちらも登録版と現在の対応表から再生成するファイルです。[件数と着手順](../docs/implementation-backlog.md)

## 診療行為マスターを取り込む

[医科診療行為マスターの配布ページ](https://www.hpdx.or.jp/seikyushiharai/tensuhyo/kihonmasta/kihonmasta_01.html)から、提供元の利用条件を確認の上で全件ファイルを取得し、公開日のフォルダに置きます。登録している版は次のとおりです。取得日は2026-11-26で、取得元URL・取得日時・サイズ・SHA-256は同フォルダの `sources.json` に記録しています。

| 資料 | 配布ページの公開日 | 保存先 |
| --- | --- | --- |
| 医科診療行為マスター・全件ファイル | 2026-11-02 | `master/2026-11-02/s_ALL20261102.zip` |
| 同日の改定分ファイルと内容説明 | 2026-11-02 | `master/2026-11-02/s_20261102.csv`、`r08kaitei_20261102_s.pdf` |
| マスターファイル仕様説明書（本編・別紙・ファイルレイアウト） | 2026-11-12 | `master/2026-11-02/spec/` |

`master/2026-11-02/tables/` には、検索用にUTF-8・LFへ変換した全件CSVを置いています。取込ツールは変換版ではなく原本ZIPを読みます。リポジトリのルートで実行してください。

```sh
python3 -m tools.procedure_master --as-of 2026-10-22
```

登録版とZIPのSHA-256を照合し、全行の列数・形式・日付・コードの重複を検査します。`--as-of` は基準とする診療日で、公開日より後の日付は指定できません。結果は次の2本で、どちらも公式データを含むためこのフォルダ内に保存します。

- `inventory/master-index.tsv`：診療行為コードごとの区分・項番、告示等識別区分、点数識別と点数、包括対象検査、判断料の群、上限回数、準用元、基準日に使用可能か。
- `inventory/master-coverage.json`：基準日に未適用の行、この版で異動のあった行、本文の区分見出しと区分欄の突合せ。突合せには先に `python3 -m tools.fee_inventory` を実行しておきます。

列の意味と読み方の注意は[参照スキーマ](../docs/tensuhyo-schema.md#医科診療行為マスター)にまとめています。区分欄が一致しても、項・注との対応や点数の一致までは確認していません。

## 条項台帳と点数照合を再生成する

公開Leanモデルの条項IDと出典、D005・D007・`SpecimenCatalog` の項目・項番・点数を出力します。Lean環境の定義を列挙し、規則リストの無名要素と有限の列挙型ごとの規則を含めます。出典を引数で受け取る補助定義は、確定した出典がない行として記録します。生成物は作業ツリーに登録せず、出力コマンドを公開します。出力はLeanのメタプログラムで値を評価して作り、モデルの定理や通常ビルドはこの評価に依存しません。

```sh
lake build
lake env lean tools/FeeLedger.lean > /tmp/sanri-lean-ledger.json
```

上のJSONは公開モデル由来です。ローカル資料との照合は、`fee-index.json` と `master-index.tsv`（版・基準日の記録は `master-coverage.json`）を同じディレクトリに配置して実行します。既存索引を再生成する場合は前節までの手順を使います。

```sh
python3 -m tools.fee_ledger
git check-ignore tensuhyo/inventory/clause-ledger.json
```

照合レポートはGit管理外の `tensuhyo/inventory/clause-ledger.json` にのみ保存します。区分別の状態、出典種別別の参照パス数、未分類一覧、区分・項番別の点数集合の一致・不一致と片側のみの行を含みます。本文の項・注の分母を取得できない区分は `null` で示します。点数比較では準用行を集計から分け、注加算を別種別として照合します。マスターの項番だけでは検査種類・枝・9桁コードを一意に対応付けられないため、一致は比較キーごとの点数集合に限ります。[条項IDの書式](../docs/tensuhyo-schema.md#公開leanモデルの条項id)

## 検体検査の外部照合を再生成する

基準診療日は2026-10-22。登録版の診療行為マスター、電子点数表、留意事項通知PDF、登録改正PDF7資料と `inventory/` のマスター・通知・改正・検体検査索引を用意します。

```sh
python3 -m tools.audit_specimen
git check-ignore tensuhyo/inventory/specimen-external-audit.json
```

同じ作業ツリーで `lake env lean tools/FeeLedger.lean > tensuhyo/inventory/specimen-lean-ledger.json` を実行し、`python3 -m tools.audit_specimen --lean-ledger specimen-lean-ledger.json` でLean台帳を再利用できます。

`tensuhyo/inventory/specimen-reviewed-names.json` は任意のローカルレビュー入力です。配列の各要素に `division`、Lean台帳の整数 `number`、NFKC正規化と空白除去を施した名称からLean項目名への `names` を記録します。構造と点数が一致する候補を原文で確認した場合に登録します。evidence 欄には同名をキーとして資料種別、PDF頁、判明した頁内行、条項ID、正規化規則を記録します。通則の加算と通知による準用の項目同定も、区分・種別・点数を確認して登録します。同じ項の枝を明示する場合は値を `item` と `branch` のオブジェクトにします。確認済みの項番・注の表記差は `number` と `kind` も指定します。準用先の単価候補は `evidence.reference_rate` に区分、準用元欄の項番、Lean台帳の項番と項目名を保持し、準用元のコード対応とは別に出力します。多対一の対応は `evidence.projection` に記録します。この絞り込みを要するコードはファイルがなければ未確定になります。

出力は `tensuhyo/inventory/specimen-external-audit.json` です。対応理由、マスター・電子表の行位置、条項候補、準用の出典探索、双方向の部分照合結果を含みます。summary の理由型別集計、未対応コードと頻度の区分別内訳、背反の区分対と理由、群別判定、包括の親コード・区分別内訳を参照できます。公式行、名称レビュー入力と出力はローカルに保持します。[検証状況](../docs/validation-status.md#検体検査の外部照合工程3a-5)

## 残尿測定の限定的なCSV照合

リポジトリのルートから実行します。対象コード・診療日・本文の共有上限と出典は、呼出元が確認して明示する入力です。スクリプト自身が本文やコード対応を公的資料から証明するわけではありません。

```sh
PYTHONDONTWRITEBYTECODE=1 python3 tools/audit_residual_urine.py \
  --ultrasound-code 160170310 \
  --catheter-code 160186710 \
  --as-of 2026-10-22 \
  --text-monthly-limit 2 \
  --text-reference '令和8年医科点数表 D216-2 注・PDF198頁; コード対応は公式資料台帳参照'
```

既定の報告先はローカルの `tensuhyo/audits/residual-urine.json` です。対象の回数・背反制約だけを取り出した射影について履歴を比較し、特例や時間単位等を解釈できない場合は未解決又はエラーを返します。この結果から、実際の算定可能性やマスター全体の誤りは結論しません。

## ライセンス・利用条件

提供元の[利用条件](https://www.hpdx.or.jp/riyo.html)には、文書・画像等の無断使用・転載の禁止が明記されています。本プロジェクトでは再配布の許諾を確認できていないため、原本ZIP・PDF・CSVだけでなく、文字コード変換版・正規化JSON・公式データの抜粋Lean等もローカルに留め、公開リポジトリや配布物には含めません。

これらの資料・データはSanriのGPLv3の適用対象外で、権利は各権利者に帰属します。GPLv3の対象外と明記することや文字コード等を変換することは、再配布の許諾を意味しません。

### 追加資料の登録と索引の再生成

令和8年度の疑義解釈・訂正・施設基準は厚生労働省の改定ページ、一部改正通知の写しは関東信越厚生局の通知一覧を参照します。[公式資料台帳](../docs/source-register.md)

`mhlw/r08/` 配下の `clarifications/`、`corrections/`、`facility/`、`amendments/` にPDFと取得元別の `sources.json` を保存します。取得一覧は `source_page`、`downloaded_at`、`downloads` を持ち、各行に `path`、`url`、`title`、`issued_on`、`bytes`、`sha256` を記録します。版を追加するときは資料台帳に出所・発出日・適用日を記録し、ファイル名とSHA-256を `tools/pdf_sources.py` に登録してください。索引の生成時に固定版のハッシュとサイズを検査します。作業ディレクトリはリポジトリのルートです。

```sh
python3 -m tools.fee_inventory
python3 -m tools.notice_inventory
python3 -m tools.procedure_master --as-of 2026-10-22
python3 -m tools.fee_ledger
python3 -m tools.r08_inventory
python3 -m tools.specimen_backlog
git check-ignore tensuhyo/mhlw/r08/{clarifications,corrections,facility,amendments}/sources.json
git check-ignore tensuhyo/inventory/{notice-revisions,notice-impact,clarification-index,facility-index,specimen-backlog}.json
```

`inventory/` に医科通知の改正・訂正位置と比較根拠を含む `notice-revisions.json`、条項台帳・準用コードとの照合を含む `notice-impact.json`、問別の `clarification-index.json`、頁数と見出し候補の `facility-index.json` を出力します。改正に新旧対照表がある場合は該当区分の見出し位置も記録し、段落の抽出には本文の改正文を用います。訂正資料の変更履歴は挿入・取消が同じテキスト層に出る箇所があり、未確定を記録します。施設基準の見出し候補はPDF上の物理頁で、告示の縦書きと通知内の階層・帳票境界はレビューが必要です。

`specimen-backlog.json` の `clarification_questions` は、基準日以前に発出された索引の医科関連の問で当該区分が明示される件数です。対象の置換を識別できた訂正前の問は除きます。索引がない場合は `null` を出力します。件数は明示区分の機械抽出範囲を表します。


改正・訂正索引があれば、`draft_fee` の `review.json` に `notice_revisions` を、同じフォルダに `revisions.txt` を出力します。登録版の抜き出しと併せて、適用済み指示、基準日後に適用される指示、訂正PDFの該当位置を確認できます。索引未生成時は索引なしと表示します。「取得済み資料の範囲では該当なし」は索引での確認結果です。

`specimen-backlog.json` の `notice_paragraph_records` は基準日の段落を `baseline`（登録版のまま）、`amended`（変更）、`added`（新設）、`deleted`（削除）で記録します。変更・新設の抽出行は `effective_records` で出典を追えます。差分の位置が曖昧な場合は要確認になります。11月適用分は `future_notice_amendments`、訂正箇所の画像確認結果は `specimen_corrections` にあります。通知参照IDの照合報告では、登録版に加えて、用いた改正文書・適用日と照合できた新設・差替え段落および枝を `matched_from_amendments` に示します。物理頁・抽出行は `effective_records` から確認できます。改正を含む段落の枝の分母は確認待ちです。
