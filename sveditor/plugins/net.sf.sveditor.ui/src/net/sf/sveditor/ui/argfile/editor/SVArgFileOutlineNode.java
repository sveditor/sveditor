package net.sf.sveditor.ui.argfile.editor;


public class SVArgFileOutlineNode {
	
	public enum NodeType {
		RootNode,
		ContentsNode,
		FileTreeNode
	};

	private NodeType			fType;
	private Object				fNode;
	private Object				fChildren[];

	public SVArgFileOutlineNode(
			NodeType		type,
			Object			node,
			Object 			children[]) {
		fType = type;
		fNode = node;
		fChildren = children;
	}
	
	public NodeType getType() {
		return fType;
	}
	
	public Object getNode() {
		return fNode;
	}

	public Object[] getChildren() {
		return fChildren;
	}
	
}
