package tree_sitter_synquid_test

import (
	"testing"

	tree_sitter "github.com/smacker/go-tree-sitter"
	"github.com/tree-sitter/tree-sitter-synquid"
)

func TestCanLoadGrammar(t *testing.T) {
	language := tree_sitter.NewLanguage(tree_sitter_synquid.Language())
	if language == nil {
		t.Errorf("Error loading Synquid grammar")
	}
}
