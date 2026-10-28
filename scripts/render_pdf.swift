import Foundation
import AppKit
import CoreText
import PDFKit

struct Source: Decodable {
    let path: String
    let title: String
    let text: String
    let sha256: String
}
struct Input: Decodable {
    let title: String
    let date: String
    let toolchain: String
    let statementCount: Int
    let auditCount: Int
    let lineCount: Int
    let bundleHash: String
    let paperHash: String
    let readme: String
    let sources: [Source]
    let config: [Source]
}
struct TextRun {
    let text: NSAttributedString
    let x: CGFloat
    let top: CGFloat
    let code: Bool
}
struct Fill {
    let rect: CGRect
    let color: NSColor
}
struct Page {
    var label: String
    var text: [TextRun] = []
    var fills: [Fill] = []
    var isCover = false
}
struct Section {
    let title: String
    let page: Int
    let group: String
}

let args = CommandLine.arguments
guard args.count == 4 else { fatalError("Usage: render_pdf.swift INPUT.json OUTPUT.pdf WORKDIR") }
let input = try JSONDecoder().decode(Input.self, from: Data(contentsOf: URL(fileURLWithPath: args[1])))
let output = URL(fileURLWithPath: args[2])
let work = URL(fileURLWithPath: args[3], isDirectory: true)
let width: CGFloat = 595.28
let height: CGFloat = 841.89
let left: CGFloat = 48
let right: CGFloat = width - 48
let bottom: CGFloat = height - 55
let bodyWidth = right - left
let navy = NSColor(srgbRed: 0.10, green: 0.18, blue: 0.27, alpha: 1)
let blue = NSColor(srgbRed: 0.12, green: 0.34, blue: 0.52, alpha: 1)
let gray = NSColor(srgbRed: 0.40, green: 0.45, blue: 0.50, alpha: 1)
let pale = NSColor(srgbRed: 0.90, green: 0.93, blue: 0.95, alpha: 1)
let comment = NSColor(srgbRed: 0.34, green: 0.43, blue: 0.37, alpha: 1)
let purple = NSColor(srgbRed: 0.44, green: 0.26, blue: 0.48, alpha: 1)

func font(_ name: String, _ size: CGFloat) -> CTFont {
    let fallback = ["STIXTwoMath", "AppleSymbols", "ArialUnicodeMS"].map {
        CTFontDescriptorCreateWithNameAndSize($0 as CFString, size)
    }
    let descriptor = CTFontDescriptorCreateWithAttributes([
        kCTFontNameAttribute: name,
        kCTFontSizeAttribute: size,
        kCTFontCascadeListAttribute: fallback,
    ] as CFDictionary)
    return CTFontCreateWithFontDescriptor(descriptor, size, nil)
}
func attr(_ text: String, _ size: CGFloat = 10.5, _ name: String = "Helvetica", _ color: NSColor = navy) -> NSAttributedString {
    NSAttributedString(string: text, attributes: [
        NSAttributedString.Key(kCTFontAttributeName as String): font(name, size),
        NSAttributedString.Key(kCTForegroundColorAttributeName as String): color.cgColor,
        NSAttributedString.Key(kCTLigatureAttributeName as String): 0,
    ])
}
func plainMarkdown(_ text: String) -> String {
    var result = text.replacingOccurrences(of: #"\[([^\]]+)\]\([^)]+\)"#, with: "$1", options: .regularExpression)
    result = result.replacingOccurrences(of: "**", with: "").replacingOccurrences(of: "`", with: "")
    return result
}
func inline(_ text: String, size: CGFloat = 10.2) -> NSAttributedString {
    let clean = text.replacingOccurrences(of: #"\[([^\]]+)\]\([^)]+\)"#, with: "$1", options: .regularExpression)
    let result = NSMutableAttributedString(string: "")
    let parts = clean.components(separatedBy: "`")
    for (i, part) in parts.enumerated() {
        result.append(attr(part.replacingOccurrences(of: "**", with: ""), i % 2 == 1 ? size * 0.91 : size,
                           i % 2 == 1 ? "Menlo-Regular" : "Helvetica", i % 2 == 1 ? blue : navy))
    }
    return result
}
func lines(_ text: NSAttributedString, width: CGFloat) -> [NSAttributedString] {
    guard text.length > 0 else { return [text] }
    let setter = CTTypesetterCreateWithAttributedString(text)
    var start = 0
    var result: [NSAttributedString] = []
    while start < text.length {
        var count = CTTypesetterSuggestLineBreak(setter, start, Double(width))
        if count == 0 { count = CTTypesetterSuggestClusterBreak(setter, start, Double(width)) }
        precondition(count > 0, "Could not wrap text")
        result.append(text.attributedSubstring(from: NSRange(location: start, length: count)))
        start += count
    }
    return result
}

var pages: [Page] = []
var sections: [Section] = []
var y: CGFloat = 70
var currentLabel = ""
var sourceFragments = 0

func newPage(_ label: String, cover: Bool = false) {
    currentLabel = label
    pages.append(Page(label: label, isCover: cover))
    y = 70
}
func room(_ need: CGFloat) {
    if y + need > bottom { newPage(currentLabel) }
}
func put(_ text: NSAttributedString, x: CGFloat = left, top: CGFloat? = nil, code: Bool = false) {
    pages[pages.count - 1].text.append(TextRun(text: text, x: x, top: top ?? y, code: code))
    if code { sourceFragments += 1 }
}
func paragraph(_ text: NSAttributedString, gap: CGFloat = 8, x: CGFloat = left, maxWidth: CGFloat = bodyWidth, leading: CGFloat = 15) {
    for line in lines(text, width: maxWidth) {
        room(leading)
        put(line, x: x)
        y += leading
    }
    y += gap
}
func heading(_ title: String, subtitle: String? = nil) {
    paragraph(attr(title, 23, "Helvetica-Bold"), gap: 11, leading: 28)
    if let subtitle { paragraph(attr(subtitle, 10.2, "Helvetica", gray), gap: 15, leading: 15) }
}
func beginSection(_ title: String, _ group: String, subtitle: String? = nil) {
    newPage(title)
    sections.append(Section(title: title, page: pages.count - 1, group: group))
    heading(title, subtitle: subtitle)
}

// Cover: a compact summary of the verified snapshot, followed by the complete source.
newPage("", cover: true)
pages[0].fills.append(Fill(rect: CGRect(x: left, y: 76, width: 46, height: 4), color: blue))
y = 110
paragraph(attr("FORMAL PROOF / VERIFIED SOURCE EDITION", 10, "Helvetica-Bold", blue), gap: 24)
paragraph(attr(input.title, 31, "Helvetica-Bold"), gap: 15, leading: 37)
paragraph(attr("Exact event accounting, conditional labor requirements,\npolicy formulas, and execution contracts", 14, "Helvetica", gray), gap: 35, leading: 20)
paragraph(attr("Lean 4.35.0 · Mathlib v4.35.0", 13, "Helvetica-Bold"), gap: 22)
let cardTop = y
pages[0].fills.append(Fill(rect: CGRect(x: left, y: cardTop, width: bodyWidth, height: 82), color: pale))
for (i, item) in [("\(input.statementCount)", "THEOREMS & LEMMAS"), ("\(input.sources.count)", "LEAN SOURCE FILES"), ("\(input.auditCount)", "DECLARATIONS AUDITED")].enumerated() {
    let x = left + 15 + CGFloat(i) * (bodyWidth / 3)
    put(attr(item.0, 25, "Helvetica-Bold"), x: x, top: cardTop + 13)
    put(attr(item.1, 8, "Helvetica-Bold", gray), x: x, top: cardTop + 53)
}
y = cardTop + 107
paragraph(attr("This edition contains the complete Lean specification and proof source, exact examples, and the axiom audit. The guide maps v6.2 equations to definitions and proofs and identifies the remaining runtime obligations.", 11), gap: 17, leading: 17)
paragraph(attr("Verification: lake --wfail build passed. The dependency audit permits only propext, Classical.choice, and Quot.sound. No additional axioms or proof placeholders occur in the proof library.", 10.4), gap: 17, leading: 16)
paragraph(attr("The formal results are conditional on their stated mathematical assumptions. Their economic interpretation and the model’s empirical validity are separate questions.", 10.4, "Helvetica", gray), gap: 14, leading: 16)
put(attr("Generated " + input.date, 9, "Helvetica", gray), top: 746)
put(attr("The PDF is a reading edition. The Lean files and compiler provide the formal certificate.", 8.5, "Helvetica", gray), top: 765)

// Reserve a page for a table of contents populated after pagination.
newPage("Contents")
let contentsPage = pages.count - 1

// Render the repository guide, preserving its correspondence table as readable entries.
beginSection("Reading guide", "Guide", subtitle: "How to build, navigate, and interpret the formalization")
let readmeLines = input.readme.components(separatedBy: .newlines)
var buffer: [String] = []
var inFence = false
func flush() {
    if !buffer.isEmpty {
        paragraph(inline(buffer.joined(separator: " ")), gap: 9, leading: 15)
        buffer.removeAll()
    }
}
for raw in readmeLines {
    if raw.hasPrefix("# ") { continue }
    if raw.hasPrefix("```") { flush(); inFence.toggle(); y += 4; continue }
    if inFence {
        paragraph(attr(raw, 9.1, "Menlo-Regular", blue), gap: 0, x: left + 12,
                  maxWidth: bodyWidth - 24, leading: 13.5)
        continue
    }
    if raw.hasPrefix("## ") {
        flush()
        let title = String(raw.dropFirst(3))
        beginSection(title, "Guide")
        continue
    }
    if raw.hasPrefix("### ") {
        flush()
        room(45)
        paragraph(attr(String(raw.dropFirst(4)), 14, "Helvetica-Bold"), gap: 10, leading: 20)
        continue
    }
    if raw.hasPrefix("| ") {
        flush()
        if raw.hasPrefix("| ---") || raw.hasPrefix("| PDF result") { continue }
        let cells = raw.split(separator: "|", omittingEmptySubsequences: true).map { $0.trimmingCharacters(in: .whitespaces) }
        if cells.count == 2 {
            room(70)
            paragraph(attr(plainMarkdown(cells[0]), 10.1, "Helvetica-Bold"), gap: 3, leading: 14)
            paragraph(inline(cells[1], size: 9.6), gap: 12, x: left + 10, maxWidth: bodyWidth - 10, leading: 14)
        }
        continue
    }
    if raw.isEmpty { flush(); continue }
    if raw.hasPrefix("- ") {
        flush()
        buffer.append("• " + String(raw.dropFirst(2)))
    } else { buffer.append(raw.trimmingCharacters(in: .whitespaces)) }
}
flush()

// Stateful, non-destructive syntax coloring; the source string itself is never rewritten.
var commentDepth = 0
func highlight(_ text: String, size: CGFloat = 8.4) -> NSAttributedString {
    let result = NSMutableAttributedString(attributedString: attr(text, size, "Menlo-Regular"))
    let ns = text as NSString
    let keyword = #"\b(?:module|public|import|namespace|end|section|open|scoped|variable|include|in|where|structure|def|noncomputable|theorem|lemma|instance|by|exact|apply|intro|rintro|have|let|show|change|rw|simp|simpa|only|using|calc|fun|funext|ext|constructor|obtain|refine|cases|induction|with|if|then|else|match|set_option|classical|norm_num|linarith|nlinarith|ring|abel|omega|decide|rfl)\b"#
    let colorKey = NSAttributedString.Key(kCTForegroundColorAttributeName as String)
    for match in try! NSRegularExpression(pattern: keyword).matches(in: text, range: NSRange(location: 0, length: ns.length)) {
        result.addAttribute(colorKey, value: blue.cgColor, range: match.range)
    }
    var i = 0
    while i < ns.length {
        let start = i
        if commentDepth > 0 || (i + 1 < ns.length && ns.substring(with: NSRange(location: i, length: 2)) == "/-") {
            if commentDepth == 0 { commentDepth = 1; i += 2 }
            while i < ns.length && commentDepth > 0 {
                let pair = i + 1 < ns.length ? ns.substring(with: NSRange(location: i, length: 2)) : ""
                if pair == "/-" { commentDepth += 1; i += 2 }
                else if pair == "-/" { commentDepth -= 1; i += 2 }
                else { i += 1 }
            }
            result.addAttribute(colorKey, value: comment.cgColor, range: NSRange(location: start, length: i - start))
        } else if i + 1 < ns.length && ns.substring(with: NSRange(location: i, length: 2)) == "--" {
            result.addAttribute(colorKey, value: comment.cgColor, range: NSRange(location: i, length: ns.length - i))
            break
        } else if ns.character(at: i) == 34 {
            i += 1
            while i < ns.length {
                if ns.character(at: i) == 92 { i = min(ns.length, i + 2) }
                else if ns.character(at: i) == 34 { i += 1; break }
                else { i += 1 }
            }
            result.addAttribute(colorKey, value: purple.cgColor, range: NSRange(location: start, length: i - start))
        } else { i += 1 }
    }
    return result
}

func sourceListing(_ source: Source, index: Int, group: String) {
    let title = group == "Source" ? String(format: "%02d  %@", index, (source.path as NSString).lastPathComponent) : source.path
    beginSection(title, group, subtitle: source.title)
    paragraph(attr(source.path, 8.5, "Menlo-Regular", gray), gap: 7, leading: 12)
    paragraph(attr("Line numbers refer to the original file. Long lines wrap without changing the source.", 8.3, "Helvetica", gray), gap: 12, leading: 12)
    commentDepth = 0
    var rawLines = source.text.components(separatedBy: "\n")
    if rawLines.last == "" { rawLines.removeLast() }
    let x = left + 30
    for (number, original) in rawLines.enumerated() {
        let styled = group == "Source" ? highlight(original) : attr(original, 8.4, "Menlo-Regular")
        let chunks = lines(styled, width: right - x)
        // Keep most logical lines together; this also prevents a lone line number at page end.
        room(min(CGFloat(chunks.count) * 12.6, 100))
        for (part, chunk) in chunks.enumerated() {
            room(12.6)
            if part == 0 { put(attr(String(number + 1), 7.4, "Menlo-Regular", gray), x: left, top: y + 0.7) }
            put(chunk, x: x, code: true)
            y += 12.6
        }
    }
    y += 16
    room(42)
    paragraph(attr("SHA-256", 7.3, "Helvetica-Bold", gray), gap: 2, leading: 10)
    paragraph(attr(source.sha256, 7.2, "Menlo-Regular", gray), gap: 0, leading: 10)
}
for (i, source) in input.sources.enumerated() { sourceListing(source, index: i + 1, group: "Source") }
for source in input.config { sourceListing(source, index: 0, group: "Configuration") }
beginSection("Snapshot provenance", "Configuration")
paragraph(inline("The listing contains all \(input.sources.count) Lean source files (\(input.lineCount) original lines), with no omitted proof bodies. All \(input.statementCount) named theorem and lemma declarations are included. The typesetting adds page furniture, line numbers, color, and wrapping only."))
paragraph(inline("Toolchain: `\(input.toolchain)`. The dependency versions are recorded in the reproduced Lake manifest. The source snapshot was built successfully using `lake --wfail build` immediately before export."))
paragraph(inline("The build’s axiom audit covered \(input.auditCount) project declarations, including generated declarations. The permitted foundations are `propext`, `Classical.choice`, and `Quot.sound`. The PDF’s inherited Python checks are separate evidence; this library does not certify a GPU engine."))
paragraph(attr("Supplied v6.2 model PDF / SHA-256", 10, "Helvetica-Bold"))
paragraph(attr(input.paperHash, 8, "Menlo-Regular"), leading: 13)
paragraph(attr("Lean source snapshot / SHA-256", 10, "Helvetica-Bold"))
paragraph(attr(input.bundleHash, 8, "Menlo-Regular"), leading: 13)
paragraph(attr("The source snapshot digest hashes each relative file path, a NUL byte, its original UTF-8 bytes, and a NUL byte, in listing order. Per-file hashes appear after each listing.", 9.5), leading: 14)
paragraph(inline("To reproduce this document on macOS, run `python3 scripts/export_pdf.py`. The script verifies the build, snapshots the source, and renders through CoreText and PDFKit. The PDF’s source text is then checked for missing glyphs and extraction fidelity."))

// Paginate the contents, then shift destinations by the inserted page count.
// Nested simulator modules make the old single-page contents insufficient.
func makeContents(_ entries: [Section]) -> [Page] {
    func emptyContents() -> Page {
        var page = Page(label: "Contents")
        page.text.append(TextRun(text: attr("Contents", 25, "Helvetica-Bold"), x: left, top: 70, code: false))
        page.text.append(TextRun(text: attr("Clickable PDF bookmarks provide the same section navigation.", 9.6, "Helvetica", gray), x: left, top: 109, code: false))
        return page
    }
    var result: [Page] = []
    var toc = emptyContents()
    var ty: CGFloat = 147
    var lastGroup = ""
    for section in entries {
        let titleLines = lines(attr(section.title, 9.7), width: bodyWidth - 40)
        let groupHeight: CGFloat = section.group == lastGroup ? 0 : 30
        if ty + groupHeight + CGFloat(titleLines.count) * 18 > bottom - 15 {
            result.append(toc)
            toc = emptyContents()
            ty = 147
            lastGroup = ""
        }
        if section.group != lastGroup {
            if !lastGroup.isEmpty { ty += 10 }
            toc.text.append(TextRun(text: attr(section.group.uppercased(), 8.3, "Helvetica-Bold", blue), x: left, top: ty, code: false))
            ty += 20
            lastGroup = section.group
        }
        toc.text.append(TextRun(text: attr(String(section.page + 1), 9.7, "Helvetica", gray), x: right - 22, top: ty, code: false))
        for line in titleLines {
            toc.text.append(TextRun(text: line, x: left, top: ty, code: false))
            ty += 18
        }
    }
    result.append(toc)
    return result
}
let extraContentsPages = makeContents(sections).count - 1
sections = sections.map { Section(title: $0.title, page: $0.page + extraContentsPages, group: $0.group) }
pages.replaceSubrange(contentsPage...contentsPage, with: makeContents(sections))

// CoreText handles Unicode fallback fonts and embeds searchable text in the PDF.
var box = CGRect(x: 0, y: 0, width: width, height: height)
let rawURL = work.appendingPathComponent("raw.pdf")
guard let context = CGContext(rawURL as CFURL, mediaBox: &box, [
    kCGPDFContextTitle: "\(input.title) — Lean Formalization",
    kCGPDFContextSubject: "Complete verified Lean 4.35.0 formalization and source guide",
    kCGPDFContextCreator: "CoreText / scripts/export_pdf.py",
] as CFDictionary) else { fatalError("Could not create PDF") }
var missingGlyphs: [String] = []
var overflow: [String] = []
func draw(_ run: TextRun, page: Int) {
    let line = CTLineCreateWithAttributedString(run.text)
    var asc: CGFloat = 0
    var desc: CGFloat = 0
    let actualWidth = CGFloat(CTLineGetTypographicBounds(line, &asc, &desc, nil) - CTLineGetTrailingWhitespaceWidth(line))
    if run.x + actualWidth > right + 1.0 && !pages[page].isCover {
        overflow.append("Page \(page + 1): \(run.text.string)")
    }
    for case let glyphRun as CTRun in CTLineGetGlyphRuns(line) as NSArray {
        let count = CTRunGetGlyphCount(glyphRun)
        var glyphs = [CGGlyph](repeating: 0, count: count)
        CTRunGetGlyphs(glyphRun, CFRange(location: 0, length: 0), &glyphs)
        if glyphs.contains(0) { missingGlyphs.append("Page \(page + 1): \(run.text.string)") }
    }
    context.textPosition = CGPoint(x: run.x, y: height - run.top - asc)
    CTLineDraw(line, context)
}
for (i, page) in pages.enumerated() {
    context.beginPDFPage(nil)
    context.setFillColor(NSColor.white.cgColor)
    context.fill(box)
    for fill in page.fills {
        context.setFillColor(fill.color.cgColor)
        let rect = fill.rect
        context.fill(CGRect(x: rect.minX, y: height - rect.maxY, width: rect.width, height: rect.height))
    }
    if !page.isCover {
        draw(TextRun(text: attr(input.title.uppercased(), 7.5, "Helvetica-Bold", gray), x: left, top: 29, code: false), page: i)
        let label = attr(page.label, 7.5, "Helvetica", gray)
        let lw = CGFloat(CTLineGetTypographicBounds(CTLineCreateWithAttributedString(label), nil, nil, nil))
        draw(TextRun(text: label, x: right - lw, top: 29, code: false), page: i)
        context.setStrokeColor(pale.cgColor)
        context.setLineWidth(0.6)
        context.move(to: CGPoint(x: left, y: height - 48))
        context.addLine(to: CGPoint(x: right, y: height - 48))
        context.strokePath()
    }
    for run in page.text { draw(run, page: i) }
    draw(TextRun(text: attr("Lean 4.35.0  /  verified source edition", 7.7, "Helvetica", gray), x: left, top: height - 33, code: false), page: i)
    draw(TextRun(text: attr("\(i + 1) / \(pages.count)", 7.7, "Helvetica", gray), x: right - 42, top: height - 33, code: false), page: i)
    context.endPDFPage()
}
context.closePDF()
guard missingGlyphs.isEmpty else { fatalError("Missing font glyphs: \(missingGlyphs.prefix(10))") }
guard overflow.isEmpty else { fatalError("Text exceeds page width: \(overflow.prefix(10))") }

guard let document = PDFDocument(url: rawURL) else { fatalError("Could not reopen PDF") }
let outline = PDFOutline()
for section in [Section(title: "Cover", page: 0, group: ""), Section(title: "Contents", page: contentsPage, group: "")] + sections {
    let item = PDFOutline()
    item.label = section.title
    item.destination = PDFDestination(page: document.page(at: section.page)!, at: CGPoint(x: 0, y: height))
    outline.insertChild(item, at: outline.numberOfChildren)
}
document.outlineRoot = outline
guard document.write(to: output) else { fatalError("Could not write final PDF") }
guard let final = PDFDocument(url: output) else { fatalError("Final PDF cannot be read") }
func normalized(_ value: String) -> String {
    value.precomposedStringWithCanonicalMapping.filter { !$0.isWhitespace }
}
var extractionFailures: [String] = []
for (i, page) in pages.enumerated() {
    let extracted = normalized(final.page(at: i)?.string ?? "")
    for run in page.text where run.code && !run.text.string.trimmingCharacters(in: .whitespaces).isEmpty {
        if !extracted.contains(normalized(run.text.string)) {
            extractionFailures.append("Page \(i + 1): \(run.text.string)")
        }
    }
}
let report: [String: Any] = [
    "pages": final.pageCount, "bookmarks": outline.numberOfChildren,
    "sourceFragments": sourceFragments, "missingGlyphs": missingGlyphs,
    "overflow": overflow, "extractionFailures": extractionFailures,
    "sections": sections.map { ["title": $0.title, "page": $0.page + 1, "group": $0.group] },
]
try JSONSerialization.data(withJSONObject: report, options: [.prettyPrinted, .sortedKeys])
    .write(to: work.appendingPathComponent("validation.json"))
guard extractionFailures.isEmpty else { fatalError("PDF text mismatch: \(extractionFailures.prefix(10))") }

// Render representative pages for a visual inspection of cover, guide, formulas and long proofs.
var selected = [0, contentsPage]
for label in ["Correspondence with the PDF", "01  MarxLeanProof.lean", "04  Spectral.lean", "12  Sensitivity.lean", "16  Examples.lean"] {
    if let section = sections.first(where: { $0.title == label }) { selected.append(section.page) }
}
for index in selected {
    let image = final.page(at: index)!.thumbnail(of: CGSize(width: width * 1.5, height: height * 1.5), for: .mediaBox)
    if let tiff = image.tiffRepresentation, let bitmap = NSBitmapImageRep(data: tiff),
       let png = bitmap.representation(using: .png, properties: [:]) {
        try png.write(to: work.appendingPathComponent(String(format: "page-%03d.png", index + 1)))
    }
}
print("PDF validated: \(final.pageCount) pages, \(outline.numberOfChildren) bookmarks, \(sourceFragments) source fragments; no missing glyphs, clipping, or source-text mismatches.")
