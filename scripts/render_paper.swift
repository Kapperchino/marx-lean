import Foundation
import AppKit
import CoreText
import PDFKit

// A small, strict MathML layout engine. KaTeX supplies the mathematical tree;
// CoreText embeds searchable glyphs. Unsupported elements cause an error.
struct Run: Decodable { let text: String; let mathml: String? }
struct Block: Decodable {
    let kind: String
    let text: String
    let number: String?
    let mathml: String?
    let runs: [Run]?
}
struct Article: Decodable {
    let blocks: [Block]
    let sourceSHA256: String
    let formulas: Int
    let katexVersion: String
}
final class Node {
    let tag: String
    let attrs: [String: String]
    var text = ""
    var children: [Node] = []
    var inheritedScriptLevel = 0
    var scriptLevel = 0
    init(_ tag: String, _ attrs: [String: String]) { self.tag = tag; self.attrs = attrs }
}
final class MathParser: NSObject, XMLParserDelegate {
    var stack: [Node] = []
    var root: Node?
    func parser(_ parser: XMLParser, didStartElement name: String, namespaceURI: String?, qualifiedName: String?, attributes: [String: String]) {
        let node = Node(name, attributes)
        node.inheritedScriptLevel = stack.last?.scriptLevel ?? 0
        node.scriptLevel = Int(attributes["scriptlevel"] ?? "") ?? node.inheritedScriptLevel
        if let parent = stack.last { parent.children.append(node) } else { root = node }
        stack.append(node)
    }
    func parser(_ parser: XMLParser, foundCharacters string: String) { stack.last?.text += string }
    func parser(_ parser: XMLParser, didEndElement name: String, namespaceURI: String?, qualifiedName: String?) { stack.removeLast() }
}
struct Glyph {
    let line: CTLine
    let text: String
    var x: CGFloat = 0
    var y: CGFloat = 0
    var sx: CGFloat = 1
    var sy: CGFloat = 1
    let width: CGFloat
    let ascent: CGFloat
    let descent: CGFloat
}
struct Rule { var x: CGFloat; var y: CGFloat; var width: CGFloat; var thickness: CGFloat }
struct Box {
    var width: CGFloat = 0
    var ascent: CGFloat = 0
    var descent: CGFloat = 0
    var glyphs: [Glyph] = []
    var rules: [Rule] = []
    mutating func add(_ box: Box, x: CGFloat = 0, y: CGFloat = 0) {
        width = max(width, x + box.width)
        ascent = max(ascent, y + box.ascent)
        descent = max(descent, box.descent - y)
        glyphs += box.glyphs.map { var g = $0; g.x += x; g.y += y; return g }
        rules += box.rules.map { var r = $0; r.x += x; r.y += y; return r }
    }
    func scaled(_ scale: CGFloat) -> Box {
        Box(width: width * scale, ascent: ascent * scale, descent: descent * scale,
            glyphs: glyphs.map { var g = $0; g.x *= scale; g.y *= scale; g.sx *= scale; g.sy *= scale; return g },
            rules: rules.map { Rule(x: $0.x * scale, y: $0.y * scale, width: $0.width * scale, thickness: $0.thickness * scale) })
    }
}

let args = CommandLine.arguments
guard args.count == 4 else { fatalError("Usage: render_paper.swift INPUT OUTPUT WORKDIR") }
let article = try JSONDecoder().decode(Article.self, from: Data(contentsOf: URL(fileURLWithPath: args[1])))
let documentTitle = article.blocks.first(where: { $0.kind == "title" })?.text ?? "Mathematical article"
let documentSubtitle = article.blocks.first(where: { $0.kind == "subtitle" })?.text.replacingOccurrences(of: "\n", with: " ") ?? ""
let output = URL(fileURLWithPath: args[2])
let work = URL(fileURLWithPath: args[3], isDirectory: true)
let pageWidth: CGFloat = 595.28, pageHeight: CGFloat = 841.89
let left: CGFloat = 64, right: CGFloat = pageWidth - 64
let bodyWidth = right - left
let pageTop: CGFloat = 62, pageBottom: CGFloat = pageHeight - 61
let bodySize: CGFloat = 11
let normal = "TimesNewRomanPSMT", italic = "TimesNewRomanPS-ItalicMT", bold = "TimesNewRomanPS-BoldMT"
var missingGlyphs: Set<String> = []
var fontCache: [String: CTFont] = [:]

func font(_ name: String, _ size: CGFloat) -> CTFont {
    let key = "\(name):\(size)"
    if let f = fontCache[key] { return f }
    let cascade = ["STIXTwoMath", "STIXTwoText", "AppleSymbols"].map { CTFontDescriptorCreateWithNameAndSize($0 as CFString, size) }
    let desc = CTFontDescriptorCreateWithAttributes([kCTFontNameAttribute: name, kCTFontSizeAttribute: size, kCTFontCascadeListAttribute: cascade] as CFDictionary)
    let result = CTFontCreateWithFontDescriptor(desc, size, nil)
    fontCache[key] = result
    return result
}
func textBox(_ text: String, _ size: CGFloat, _ name: String = "TimesNewRomanPSMT") -> Box {
    if text.isEmpty { return Box() }
    let attr = NSAttributedString(string: text, attributes: [
        NSAttributedString.Key(kCTFontAttributeName as String): font(name, size),
        NSAttributedString.Key(kCTForegroundColorAttributeName as String): NSColor.black.cgColor,
    ])
    let line = CTLineCreateWithAttributedString(attr)
    var asc: CGFloat = 0, desc: CGFloat = 0
    let width = CGFloat(CTLineGetTypographicBounds(line, &asc, &desc, nil))
    for case let run as CTRun in CTLineGetGlyphRuns(line) as NSArray {
        var glyphs = [CGGlyph](repeating: 0, count: CTRunGetGlyphCount(run))
        CTRunGetGlyphs(run, CFRange(location: 0, length: 0), &glyphs)
        if glyphs.contains(0) { missingGlyphs.insert(text) }
    }
    return Box(width: width, ascent: asc, descent: desc, glyphs: [Glyph(line: line, text: text, width: width, ascent: asc, descent: desc)])
}
func horizontal(_ boxes: [Box]) -> Box {
    var result = Box()
    for box in boxes { let x = result.width; result.add(box, x: x) }
    return result
}
func length(_ value: String?, size: CGFloat, fallback: CGFloat) -> CGFloat {
    guard let value else { return fallback }
    let first = value.components(separatedBy: " ")[0]
    if first.hasSuffix("em"), let n = Double(first.dropLast(2)) { return CGFloat(n) * size }
    if let n = Double(first) { return CGFloat(n) }
    fatalError("Unsupported MathML length: \(value)")
}
func math(_ node: Node, _ size: CGFloat, _ display: Bool) -> Box {
    let c = node.children.filter { $0.tag != "annotation" }
    switch node.tag {
    case "annotation": return Box()
    case "math", "semantics", "mrow", "mtd":
        var boxes = c.map { math($0, size, display) }
        let ascent = max(size * 0.75, boxes.map(\.ascent).max() ?? 0)
        let descent = max(size * 0.20, boxes.map(\.descent).max() ?? 0)
        for (i, child) in c.enumerated() where child.tag == "mo" && child.attrs["stretchy"] != "false" {
            if ["(", ")", "[", "]", "{", "}", "|", "‖", "∥"].contains(child.text) && ascent + descent > size * 1.2 {
                var b = textBox(child.text, size, "STIXTwoMath")
                let target = ascent + descent + size * 0.12
                let factor = target / (b.ascent + b.descent)
                let shift = (ascent - descent) / 2 - (b.ascent - b.descent) * factor / 2
                b.glyphs = b.glyphs.map { var g = $0; g.sy *= factor; g.y += shift; return g }
                b.ascent = ascent + size * 0.06
                b.descent = descent + size * 0.06
                b.width += size * 0.12
                boxes[i] = b
            }
        }
        return horizontal(boxes)
    case "mstyle":
        let delta = node.scriptLevel - node.inheritedScriptLevel
        let s = size * pow(0.72, CGFloat(delta))
        return horizontal(c.map { math($0, s, node.attrs["displaystyle"].map { $0 == "true" } ?? display) })
    case "mi", "mn", "mo", "mtext":
        var value = node.text
        if value == "⁡" { return Box(width: size * 0.08) }
        let variant = node.attrs["mathvariant"] ?? ""
        var name = "STIXTwoMath"
        if node.tag == "mi" && variant.isEmpty && value.count == 1 { name = italic }
        if node.tag == "mi" && value.count > 1 { name = normal }
        if node.tag == "mtext" || variant == "normal" { name = normal }
        if variant == "bold" { name = bold }
        if variant == "sans-serif" { name = "Helvetica" }
        if variant == "double-struck" { value = ["R": "ℝ", "N": "ℕ", "Q": "ℚ", "Z": "ℤ", "C": "ℂ"][value] ?? value }
        if variant == "script" { value = ["A": "𝒜"][value] ?? value }
        var result = textBox(value, size, name)
        var padding: CGFloat = 0
        if node.tag == "mo" {
            if ["=", "<", ">", "≤", "≥", "≪", "≫", "∈"].contains(value) { padding = size * 0.22 }
            else if ["+", "−", "×", "∨", "∧", "⊙"].contains(value) { padding = size * 0.15 }
            else if value == "," { result.width += size * 0.12 }
        }
        if padding > 0 {
            var padded = Box(width: padding * 2 + result.width)
            padded.add(result, x: padding)
            result = padded
        }
        return result
    case "mspace": return Box(width: length(node.attrs["width"], size: size, fallback: 0))
    case "msup", "msub", "msubsup":
        let base = math(c[0], size, display)
        var result = base
        let scriptSize = size * 0.69
        let x = base.width + size * 0.035
        if node.tag == "msup" || node.tag == "msubsup" {
            let upper = math(c[node.tag == "msup" ? 1 : 2], scriptSize, false)
            let y = max(size * 0.38, base.ascent - size * 0.55) + upper.descent
            result.add(upper, x: x, y: y)
        }
        if node.tag == "msub" || node.tag == "msubsup" {
            let lower = math(c[1], scriptSize, false)
            let down = max(size * 0.23, base.descent + size * 0.08)
            result.add(lower, x: x, y: -down)
        }
        result.width += size * 0.04
        return result
    case "mfrac":
        let s = size * (display ? 0.93 : 0.78)
        let num = math(c[0], s, false), den = math(c[1], s, false)
        let width = max(num.width, den.width) + size * 0.35
        let axis = size * 0.24, gap = size * 0.20
        var result = Box(width: width)
        result.add(num, x: (width - num.width) / 2, y: axis + gap + num.descent)
        result.add(den, x: (width - den.width) / 2, y: axis - gap - den.ascent)
        result.rules.append(Rule(x: size * 0.07, y: axis, width: width - size * 0.14, thickness: max(0.35, size * 0.042)))
        return result
    case "munder", "munderover":
        let base = math(c[0], size * (display && c[0].tag == "mo" ? 1.25 : 1), display)
        let lower = math(c[1], size * 0.66, false)
        let upper = c.count > 2 ? math(c[2], size * 0.66, false) : Box()
        let width = max(base.width, lower.width, upper.width) + size * 0.1
        var result = Box(width: width)
        result.add(base, x: (width - base.width) / 2)
        result.add(lower, x: (width - lower.width) / 2, y: -base.descent - size * 0.12 - lower.ascent)
        if c.count > 2 { result.add(upper, x: (width - upper.width) / 2, y: base.ascent + size * 0.1 + upper.descent) }
        return result
    case "mover":
        let base = math(c[0], size, display)
        var result = base
        if ["‾", "¯", "―"].contains(c[1].text) {
            result.rules.append(Rule(x: 0, y: base.ascent + size * 0.10, width: base.width, thickness: size * 0.04))
            result.ascent += size * 0.18
        } else {
            let accent = textBox(c[1].text, size * 0.8, "STIXTwoMath")
            result.add(accent, x: max(0, (base.width - accent.width) / 2), y: base.ascent - accent.descent - size * 0.32)
        }
        return result
    case "mtable":
        let rows = c.map { row in row.children.map { math($0, size, display) } }
        let count = rows.map(\.count).max() ?? 0
        var widths = [CGFloat](repeating: 0, count: count)
        for row in rows { for (j, b) in row.enumerated() { widths[j] = max(widths[j], b.width) } }
        let gap = length(node.attrs["columnspacing"], size: size, fallback: size)
        let rowGap = max(size * 0.32, length(node.attrs["rowspacing"], size: size, fallback: size * 0.3))
        let asc = rows.map { max(size * 0.72, $0.map(\.ascent).max() ?? 0) }
        let des = rows.map { max(size * 0.20, $0.map(\.descent).max() ?? 0) }
        let height = zip(asc, des).reduce(CGFloat(0)) { $0 + $1.0 + $1.1 } + CGFloat(max(0, rows.count - 1)) * rowGap
        let top = height / 2 + size * 0.25
        var result = Box(width: widths.reduce(0,+) + CGFloat(max(0,count-1)) * gap, ascent: top, descent: max(0, height-top))
        let aligns = (node.attrs["columnalign"] ?? "center").components(separatedBy: " ")
        var y = top
        for (i, row) in rows.enumerated() {
            y -= asc[i]
            var x: CGFloat = 0
            for (j, b) in row.enumerated() {
                let align = aligns[min(j, aligns.count-1)]
                let offset = align == "right" ? widths[j] - b.width : align == "left" ? 0 : (widths[j] - b.width)/2
                result.add(b, x: x + offset, y: y)
                x += widths[j] + gap
            }
            y -= des[i] + rowGap
        }
        return result
    default: fatalError("Unsupported MathML element: \(node.tag)")
    }
}
var mathCache: [String: Box] = [:]
func mathBox(_ xml: String, _ size: CGFloat, display: Bool = false) -> Box {
    let key = "\(size):\(display):\(xml)"
    if let result = mathCache[key] { return result }
    let parser = XMLParser(data: xml.data(using: .utf8)!)
    let delegate = MathParser()
    parser.delegate = delegate
    guard parser.parse(), let root = delegate.root else { fatalError("Invalid MathML: \(parser.parserError.debugDescription)") }
    let result = math(root, size, display)
    mathCache[key] = result
    return result
}

struct Placement { let box: Box; let x: CGFloat; let baseline: CGFloat; let kind: String }
struct Page { var placements: [Placement] = []; var label = "" }
struct Bookmark { let title: String; let page: Int; let top: CGFloat }
var pages = [Page()]
var bookmarks: [Bookmark] = []
var currentLabel = documentTitle
var y = pageTop
var overflows: [String] = []
var equationScales: [[String: Any]] = []
var paragraphCount = 0

func newPage() { pages.append(Page(label: currentLabel)); y = pageTop }
func room(_ height: CGFloat) { if y + height > pageBottom { newPage() } }
func place(_ box: Box, x: CGFloat, baseline: CGFloat, kind: String) {
    if x < left - 0.5 || x + box.width > right + 0.5 || baseline - box.ascent < pageTop - 1 || baseline + box.descent > pageBottom + 0.5 {
        overflows.append("Page \(pages.count), \(kind), bounds \(x),\(baseline-box.ascent),\(box.width),\(box.ascent+box.descent)")
    }
    pages[pages.count-1].placements.append(Placement(box: box, x: x, baseline: baseline, kind: kind))
}
struct Word { var box: Box; let space: Bool }
func words(_ runs: [Run], size: CGFloat, name: String) -> [Word] {
    var result: [Word] = []
    for run in runs {
        if let xml = run.mathml {
            result.append(Word(box: mathBox(xml, size), space: false))
        } else {
            let regex = try! NSRegularExpression(pattern: #"\s+|\S+"#)
            let ns = run.text as NSString
            for match in regex.matches(in: run.text, range: NSRange(location: 0, length: ns.length)) {
                let value = ns.substring(with: match.range)
                let space = value.first?.isWhitespace == true
                result.append(Word(box: textBox(space ? " " : value, size, name), space: space))
            }
        }
    }
    // Join adjacent nonspace pieces so punctuation stays attached to formulas.
    var joined: [Word] = []
    for word in result {
        if !word.space, let last = joined.last, !last.space {
            joined[joined.count-1].box = horizontal([last.box, word.box])
        } else { joined.append(word) }
    }
    return joined
}
func paragraphHeight(_ runs: [Run], size: CGFloat = bodySize, name: String = "TimesNewRomanPSMT") -> CGFloat {
    var width: CGFloat = 0, ascent: CGFloat = 0, descent: CGFloat = 0, height: CGFloat = 0
    for word in words(runs, size: size, name: name) {
        if width == 0 && word.space { continue }
        if !word.space && width + word.box.width > bodyWidth && width > 0 {
            height += max(size * 1.38, ascent + descent + size * 0.23)
            width = 0; ascent = 0; descent = 0
        }
        width += word.box.width
        ascent = max(ascent, word.box.ascent); descent = max(descent, word.box.descent)
    }
    if width > 0 { height += max(size * 1.38, ascent + descent + size * 0.23) }
    return height + 7
}
func paragraph(_ runs: [Run], size: CGFloat = bodySize, name: String = "TimesNewRomanPSMT", indent: CGFloat = 0, gap: CGFloat = 7, justified: Bool = true, centered: Bool = false, kind: String = "paragraph", trailingReserve: CGFloat = 0) {
    let available = bodyWidth - 2 * indent
    let tokens = words(runs, size: size, name: name)
    var lines: [[Word]] = [], line: [Word] = [], used: CGFloat = 0
    for word in tokens {
        if line.isEmpty && word.space { continue }
        if !word.space && used + word.box.width > available && !line.isEmpty {
            while line.last?.space == true { line.removeLast() }
            lines.append(line)
            line = []; used = 0
        }
        line.append(word); used += word.box.width
    }
    while line.last?.space == true { line.removeLast() }
    if !line.isEmpty { lines.append(line) }
    let heights = lines.map { row -> CGFloat in
        max(size * 1.38, (row.map { $0.box.ascent }.max() ?? 0) + (row.map { $0.box.descent }.max() ?? 0) + size * 0.23)
    }
    // Keep short paragraphs intact and prevent a lone first or last line.
    if lines.count <= 3 { room(heights.reduce(0,+) + gap + trailingReserve) }
    else { room(heights.prefix(2).reduce(0,+)) }
    for (i, row) in lines.enumerated() {
        if i == lines.count - 2 { room(heights.suffix(2).reduce(0,+) + gap + trailingReserve) }
        else if i == lines.count - 1 { room(heights[i] + gap + trailingReserve) }
        else { room(heights[i]) }
        let total = row.reduce(CGFloat(0)) { $0 + $1.box.width }
        let gaps = row.filter(\.space).count
        let extra = justified && i < lines.count - 1 && gaps > 0 ? max(0,(available-total)/CGFloat(gaps)) : 0
        let asc = row.map { $0.box.ascent }.max() ?? 0
        let baseline = y + asc
        var x = left + indent + (centered ? (available-total)/2 : 0)
        for word in row {
            if !word.space { place(word.box, x: x, baseline: baseline, kind: kind) }
            x += word.box.width + (word.space ? extra : 0)
        }
        y += heights[i]
    }
    y += gap
    paragraphCount += 1
}
func plain(_ text: String, size: CGFloat, name: String = "TimesNewRomanPSMT", gap: CGFloat = 7, centered: Bool = false, kind: String = "text") {
    paragraph([Run(text: text, mathml: nil)], size: size, name: name, gap: gap, justified: false, centered: centered, kind: kind)
}

for (index, block) in article.blocks.enumerated() {
    switch block.kind {
    case "title":
        y += 8
        plain(block.text, size: 21, name: bold, gap: 12, centered: true, kind: "title")
    case "subtitle":
        for line in block.text.components(separatedBy: "\n") { plain(line, size: 12.5, gap: 1, centered: true, kind: "subtitle") }
        y += 9
    case "date": plain(block.text, size: 10.5, gap: 21, centered: true, kind: "date")
    case "abstract_heading": plain(block.text, size: 11, name: bold, gap: 6, centered: true)
    case "abstract": paragraph(block.runs ?? [], size: 10.3, indent: 16, gap: 17)
    case "section":
        room(85)
        y += 9
        currentLabel = block.text
        bookmarks.append(Bookmark(title: block.text, page: pages.count - 1, top: y))
        plain(block.text, size: 13.1, name: bold, gap: 10, kind: "section")
    case "statement":
        var required = paragraphHeight(block.runs ?? [], name: bold) + 8
        // Keep a theorem's hypotheses and conclusion together when they fit on a page.
        for following in article.blocks.dropFirst(index + 1) {
            if following.kind == "paragraph" {
                required += paragraphHeight(following.runs ?? [])
            } else if following.kind == "equation" {
                let equation = mathBox(following.mathml!, 11.6, display: true)
                required += equation.ascent + equation.descent + 31
            } else {
                break
            }
        }
        room(max(68, min(required, pageBottom - pageTop)))
        y += 4
        plain(block.text, size: 11, name: bold, gap: 4, kind: "statement")
    case "proof":
        room(48)
        plain(block.text, size: bodySize, name: italic, gap: 2, kind: "proof")
    case "qed":
        let q = textBox("□", 9, "STIXTwoMath")
        if let last = pages.last?.placements.last, last.kind == "paragraph", last.x + last.box.width < right - q.width - 5 {
            place(q, x: right - q.width, baseline: last.baseline, kind: "qed")
            y += 3
        } else {
            room(q.ascent + q.descent)
            place(q, x: right - q.width, baseline: y + q.ascent, kind: "qed")
            y += q.ascent + q.descent + 3
        }
    case "equation":
        var b = mathBox(block.mathml!, 11.6, display: true)
        let maxWidth = bodyWidth - 38
        let scale = min(1, maxWidth / b.width)
        if scale < 0.84 { fatalError("Equation \(block.number!) is too wide; split it in the source. Scale \(scale)") }
        if scale < 1 { b = b.scaled(scale) }
        equationScales.append(["number": block.number!, "scale": scale, "width": b.width])
        let h = b.ascent + b.descent + 15
        // Reserve a line after a displayed equation when prose follows.
        room(h + (index+1 < article.blocks.count && article.blocks[index+1].kind == "paragraph" ? 16 : 0))
        let baseline = y + 6 + b.ascent
        place(b, x: left + (bodyWidth - b.width) / 2, baseline: baseline, kind: "equation \(block.number!)")
        let tag = textBox("(\(block.number!))", 10, normal)
        place(tag, x: right - tag.width, baseline: baseline + (b.descent-b.ascent)/2 + 3, kind: "equation number")
        y += h
    case "paragraph":
        var reserve: CGFloat = 0
        if index+1 < article.blocks.count, article.blocks[index+1].kind == "equation" {
            let next = mathBox(article.blocks[index+1].mathml!, 11.6, display: true)
            reserve = next.ascent + next.descent + 15
            if index+2 < article.blocks.count, article.blocks[index+2].kind == "paragraph" { reserve += 16 }
        }
        paragraph(block.runs ?? [], trailingReserve: reserve)
    default: fatalError("Unsupported article block: \(block.kind)")
    }
}
guard missingGlyphs.isEmpty else { fatalError("Missing glyphs: \(missingGlyphs)") }
guard overflows.isEmpty else { fatalError("Layout overflow: \(overflows.prefix(12))") }

var media = CGRect(x: 0, y: 0, width: pageWidth, height: pageHeight)
let raw = work.appendingPathComponent("raw.pdf")
let context = CGContext(raw as CFURL, mediaBox: &media, [
    kCGPDFContextTitle: documentTitle,
    kCGPDFContextSubject: documentSubtitle,
    kCGPDFContextCreator: "KaTeX MathML / CoreText mathematical article exporter",
] as CFDictionary)!
func draw(_ box: Box, x: CGFloat, baseline: CGFloat) {
    for g in box.glyphs {
        context.saveGState()
        context.translateBy(x: x + g.x, y: pageHeight - baseline + g.y)
        context.scaleBy(x: g.sx, y: g.sy)
        context.textPosition = .zero
        CTLineDraw(g.line, context)
        context.restoreGState()
    }
    for r in box.rules {
        context.setStrokeColor(NSColor.black.cgColor)
        context.setLineWidth(r.thickness)
        context.move(to: CGPoint(x: x+r.x, y: pageHeight-baseline+r.y))
        context.addLine(to: CGPoint(x: x+r.x+r.width, y: pageHeight-baseline+r.y))
        context.strokePath()
    }
}
for (i, page) in pages.enumerated() {
    context.beginPDFPage(nil)
    context.setFillColor(NSColor.white.cgColor); context.fill(media)
    if i > 0 {
        draw(textBox(documentTitle, 8.5, italic), x: left, baseline: 37)
        let running = textBox("Mathematical exposition", 8.5, italic)
        draw(running, x: right-running.width, baseline: 37)
    }
    for item in page.placements { draw(item.box, x: item.x, baseline: item.baseline) }
    let number = textBox("\(i+1)", 10)
    draw(number, x: (pageWidth-number.width)/2, baseline: pageHeight-32)
    context.endPDFPage()
}
context.closePDF()
guard let document = PDFDocument(url: raw) else { fatalError("Cannot reopen PDF") }
let outline = PDFOutline()
for bookmark in bookmarks {
    let entry = PDFOutline()
    entry.label = bookmark.title
    entry.destination = PDFDestination(page: document.page(at: bookmark.page)!, at: CGPoint(x: left, y: pageHeight-bookmark.top+12))
    outline.insertChild(entry, at: outline.numberOfChildren)
}
document.outlineRoot = outline
guard document.write(to: output), let final = PDFDocument(url: output) else { fatalError("Cannot save final PDF") }
let allText = (0..<final.pageCount).map { final.page(at: $0)?.string ?? "" }.joined(separator: "\n\n")
try allText.write(to: work.appendingPathComponent("extracted.txt"), atomically: true, encoding: .utf8)
// Font encodings can map Greek mu to the compatibility-equivalent micro sign.
func normalized(_ text: String) -> String { text.precomposedStringWithCompatibilityMapping.filter { !$0.isWhitespace } }
var extractionFailures: [String] = []
for (index, page) in pages.enumerated() {
    let extracted = normalized(final.page(at: index)?.string ?? "")
    for placement in page.placements {
        for glyph in placement.box.glyphs {
            let expected = normalized(glyph.text)
            if !expected.isEmpty && !extracted.contains(expected) { extractionFailures.append("Page \(index+1): \(glyph.text)") }
        }
    }
}
let report: [String: Any] = [
    "pages": final.pageCount, "formulas": article.formulas, "equations": equationScales.count,
    "sourceSHA256": article.sourceSHA256, "katexVersion": article.katexVersion,
    "missingGlyphs": Array(missingGlyphs), "overflow": overflows,
    "equationScales": equationScales,
    "sections": bookmarks.map { ["title": $0.title, "page": $0.page+1] },
    "paragraphBlocks": paragraphCount, "extractedCharacters": allText.count,
    "extractionFailures": extractionFailures,
    "textComparisonNormalization": "Unicode NFKC with whitespace omitted",
]
try JSONSerialization.data(withJSONObject: report, options: [.prettyPrinted, .sortedKeys]).write(to: work.appendingPathComponent("validation.json"))
// Every page is rendered so that layout can be inspected independently of text extraction.
for file in try FileManager.default.contentsOfDirectory(at: work, includingPropertiesForKeys: nil) {
    if file.lastPathComponent.range(of: #"^page-\d+\.png$"#, options: .regularExpression) != nil { try FileManager.default.removeItem(at: file) }
}
for index in 0..<final.pageCount {
    let image = final.page(at: index)!.thumbnail(of: CGSize(width: pageWidth*1.5, height: pageHeight*1.5), for: .mediaBox)
    if let tiff = image.tiffRepresentation, let bitmap = NSBitmapImageRep(data: tiff), let png = bitmap.representation(using: .png, properties: [:]) {
        try png.write(to: work.appendingPathComponent(String(format: "page-%02d.png", index+1)))
    }
}
guard extractionFailures.isEmpty else { fatalError("PDF text extraction mismatches: \(extractionFailures.prefix(20))") }
print("Validated \(final.pageCount) pages, \(article.formulas) formulas, \(equationScales.count) displayed equations; no missing glyphs, page-boundary overflow, or text extraction mismatches.")
