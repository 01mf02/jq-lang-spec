#let mainFont = "Linux Libertine O"
#let sfFont = "Linux Biolinum O"

#let show-month(month) = (
  "January",
  "February",
  "March",
  "April",
  "May",
  "June",
  "July",
  "August",
  "September",
  "October",
  "November",
  "December"
).at(month - 1)

#let author-address(author) = {
  author.name
  if author.at("email", default: none) != none [, #author.email]
}

#let author-groups(authors) = {
  let groups = ()
  // affiliation of the current group
  let affiliation = none
  for author in authors {
    // if affiliation changes, start a new group
    if author.affiliation != affiliation {
      groups.push(())
      affiliation = author.affiliation
    }
    if groups == () { groups.push(()) }
    groups.last().push(author)
  }
  groups
}

// Display a group of authors with the same affiliation
#let show-author-group(group) = {
  text(font: sfFont, size: 11pt, group.map(author => upper(author.name)).join(", ", last: " and "))
  let affiliation = group.first().affiliation
  if affiliation != none {
    text(font: mainFont, size: 9pt)[, #affiliation.institution, #affiliation.country]
  }
}

#let show-subconcept(priority, name) = {
  if priority >= 500 {
    strong(name)
  } else if priority >= 300 {
    emph(name)
  } else {
    name
  }
}

#let show-ccs(concept) = [
  #box(baseline: -50%, circle(radius: 1.25pt, fill: black)) *#concept.at(0)* $->$
  #concept.at(1).map(subconcept => show-subconcept(subconcept.at(0), subconcept.at(1))).join("; ")
]

#let legal(acm) = [
  Permission to make digital or hard copies of all or part of this
  work for personal or classroom use is granted without fee provided
  that copies are not made or distributed for profit or commercial
  advantage and that copies bear this notice and the full citation on
  the first page. Copyrights for components of this work owned by
  others than ACM must be honored. Abstracting with credit is
  permitted. To copy otherwise, or republish, to post on servers or to
  redistribute to lists, requires prior specific permission
  and#h(.5pt)/or  a fee. Request permissions from
  permissions\@acm.org.\
  #sym.copyright #acm.year Association for Computing Machinery\
  0004-5411/2018/8-ART1 \$15.00\
  https:\/\/doi.org\/#acm.doi
]

#let even-page(loc) = calc.rem(loc.page(), 2) == 0

#let acmart(
  // Currently supported formats are:
  //  - acmsmall
  format: "acmsmall",
  
  // Title, subtitle, authors, abstract, ACM ccs, keywords
  title: "Title",
  subtitle: none,
  shorttitle: none,
  authors: (),
  shortauthors: none,
  abstract: none,
  ccs: none,
  keywords: none,

  acm: (
    journal: none,
    volume: 1,
    number: 1,
    article: none,
    month: 5,
    year: 2023,
    doi: "XXXXXXX.XXXXXXX",
  ),

  body
) = {
  let journal = if acm.journal == "JACM" {
    (
      name: "Journal of the ACM",
      nameShort: "J. ACM"
    )
  } else {
    none
  }

  if shorttitle == none {
    shorttitle = title
  }

  if shortauthors == none {
    shortauthors = authors.map(author => author.name).join(", ", last: " and ")
  }

  let footer = [
    #journal.nameShort,
    Vol. #acm.volume,
    No. #acm.number,
    Article #acm.article.
    Publication date: #show-month(acm.month) #acm.year.
  ]

  let header(loc) = {
    let article_page = [#acm.article:#counter(page).display()]
    if even-page(loc) [#article_page #h(1fr) #shortauthors]
    else [#shorttitle #h(1fr) #article_page]
  }

  // Set document metadata
  set document(title: title, author: authors.map(author => author.name))

  // Configure the page.
  set page(
    width:  6.75in,
    height: 10in,
    margin: (
      top: 58pt + 27pt,
      bottom: 39pt + 24pt,
      left: 46pt,
      right: 46pt
    ),
    header: text(size: 8pt, font: sfFont, locate(loc => if loc.page() > 1 { header(loc) })),
    footer: text(size: 8pt, locate(loc => align(if even-page(loc) { left } else { right }, footer))),
    header-ascent: 17pt,
    footer-descent: 24pt,
  )

  // title page
  {
    set text(size: 9pt)
    set par(justify: true, leading: 0.555em)
    show par: set block(below: 9.5pt)

    // Display title
    text(font: sfFont, size: 14.4pt, weight: "bold", title)
    v(7pt)

    author-groups(authors).map(show-author-group).join("\n")
    footnote([Authors' addresses: #authors.map(author-address).join("; ").])
    v(2.5pt)

    [
      #abstract

      CCS Concepts: #ccs.map(c => show-ccs(c)).join("; ").

      Additional Key Words and Phrases: #keywords.join(", ")

      *ACM Reference Format:* \
      #authors.map(author => author.name).join(", ", last: " and ").
      #acm.year.
      #title.
      #emph(journal.nameShort)
      #acm.volume,
      #acm.number,
      Article #acm.article (#show-month(acm.month) #acm.year),
      #counter(page).display((..nums) => [
        #nums.pos().last() page#if(nums.pos().last() > 1) { [s] }.
      ],both: true)
      https:\/\/doi.org\/#acm.doi
      #footnote(legal(acm))
    ]

    v(1pt)
  }

  set text(font: mainFont, size: 10pt)

  set heading(numbering: "1.1")
  show heading: it => block(text(font: sfFont, size: 10pt, weight: "bold", {
    if it.numbering != none {
      box(width: 15pt, counter(heading).display())
    }
    upper(it.body)
  }))

  set par(
    justify: true,
    leading: 5.35pt,
    first-line-indent: 9.5pt)
  show par: set block(below: 5.35pt)

  body
}
