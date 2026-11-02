"""
Dependency-graph colours for this blueprint (loaded by `\\usepackage{gspincolors}` in web.tex).

leanblueprint's standard scheme colours a node dark green when its proof and all its ancestors are
formalized, and gives no special colour to results assumed from the literature (Lean `axiom`s),
which then look like unproved statements. This package keeps the standard colours and adds:

* literature results (the `literature` environment): their own fill and border;
* proved results whose ancestors are all proved or literature results, with at least one literature
  ancestor: "proved, modulo the literature";
* `\\mathlibok` nodes (available in Mathlib or Tau Ceti, restated here) get a slate grey fill;
* all borders are drawn bold, so the border colours are easier to read.

Dark green fill still means fully formalized: no `sorry` and no literature assumption anywhere
below the node.
"""
from plastexdepgraph.Packages.depgraph import item_kind

LITERATURE_FILL = '#E3D3F5'
LITERATURE_BORDER = '#7E57C2'
MOD_LITERATURE_FILL = '#F6D66B'
LIBRARY_FILL = '#C5CBD3'


def ProcessOptions(options, document):
    colors = document.userdata['dep_graph']['colors']
    colors['literature'] = (LITERATURE_FILL, 'Lavender')
    colors['literature_border'] = (LITERATURE_BORDER, 'Purple')
    colors['mod_literature'] = (MOD_LITERATURE_FILL, 'Gold')
    colors['library'] = (LIBRARY_FILL, 'Slate grey')

    std_colorizer = document.userdata['dep_graph']['colorizer']
    std_fillcolorizer = document.userdata['dep_graph']['fillcolorizer']

    def is_literature(node) -> bool:
        return item_kind(node) == 'literature'

    def compute() -> None:
        for graph in document.userdata['dep_graph']['graphs'].values():
            for node in graph.nodes:
                ancestors = graph.ancestors(node).union({node})
                ok = all(n.userdata.get('proved', False) or item_kind(n) == 'definition'
                         or is_literature(n) for n in ancestors)
                node.userdata['proved_mod_literature'] = (
                    ok and node.userdata.get('proved', False)
                    and any(is_literature(n) for n in ancestors))

    def colorizer(node) -> str:
        if is_literature(node):
            return LITERATURE_BORDER
        return std_colorizer(node)

    def fillcolorizer(node) -> str:
        if is_literature(node):
            return LITERATURE_FILL
        if node.userdata.get('mathlibok'):
            return LIBRARY_FILL
        if node.userdata.get('proved_mod_literature'):
            return MOD_LITERATURE_FILL
        return std_fillcolorizer(node)

    def stylerizer(node) -> str:
        # Bold borders, so that border colours (statement status) are easier to tell apart.
        return 'filled,bold' if fillcolorizer(node) else 'bold'

    document.userdata['dep_graph']['colorizer'] = colorizer
    document.userdata['dep_graph']['fillcolorizer'] = fillcolorizer
    document.userdata['dep_graph']['stylerizer'] = stylerizer

    def make_legend() -> None:
        legend = document.userdata['dep_graph']['legend']
        legend[:] = [(k, v.replace('this is in Mathlib',
                                   'this is available in Mathlib or Tau Ceti (restated here)'))
                     for k, v in legend]
        legend.extend([
            ('Lavender background, purple border',
             'a result <em>assumed from the literature</em> (a Lean axiom citing its source)'),
            ('Slate grey background',
             'available in Mathlib or Tau Ceti and restated here (proved from the library)'),
            ('Gold background',
             'the <em>proof</em> of this result is formalized, and everything below it is formalized '
             'or assumed from the literature (no unproved steps, but it rests on the literature)'),
        ])

    # After leanblueprint's own callbacks (order 150).
    document.addPostParseCallbacks(160, compute)
    document.addPostParseCallbacks(160, make_legend)
