package net.sf.sveditor.ui.search;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.search.ui.text.AbstractTextSearchResult;

public class SVSearchTreeContentProvider implements ITreeContentProvider {
	private static final Object			EMPTY[] = new Object[0];
	private Map<Object, Set<Object>>	fChildrenMap;
	private AbstractTextSearchResult	fResult;
	private TreeViewer					fTreeViewer;
	
	public SVSearchTreeContentProvider(SVSearchResultsPage page, TreeViewer viewer) {
		fTreeViewer = viewer;
	}

	public void dispose() {
		// TODO Auto-generated method stub

	}

	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		// TODO Auto-generated method stub
		initialize((AbstractTextSearchResult)newInput);
	}
	
	private void initialize(AbstractTextSearchResult result) {
		fResult = result;
		fChildrenMap= new HashMap<Object, Set<Object>>();
		// boolean showLineMatches= true; // !((FileSearchQuery) fResult.getQuery()).isFileNameSearch();
		
		if (result != null) {
			Object[] elements = result.getElements();
			for (int i= 0; i < elements.length; i++) {
				/*
				if (showLineMatches) {
					Match[] matches= result.getMatches(elements[i]);
					for (int j= 0; j < matches.length; j++) {
						insert(((FileMatch) matches[j]).getLineElement(), false);
					}
				} else {
				 */
					insert(elements[i], false);
//				}
			}
		}
	}
	
	private void insert(Object child, boolean refreshViewer) {
		Object parent = getParent(child);
		while (parent != null) {
			if (insertChild(parent, child)) {
				if (refreshViewer && !fTreeViewer.getControl().isDisposed()) {
					fTreeViewer.add(parent, child);
				}
			} else {
				if (refreshViewer && !fTreeViewer.getControl().isDisposed()) {
					fTreeViewer.refresh(parent);
				}
				return;
			}
			child = parent;
			parent = getParent(child);
		}
		if (insertChild(fResult, child)) {
			if (refreshViewer && !fTreeViewer.getControl().isDisposed()) {
				fTreeViewer.add(fResult, child);
			}
		}
	}
	
	private void remove(Object element, boolean refreshViewer) {
		// precondition here:  fResult.getMatchCount(child) <= 0
	
		if (hasChildren(element)) {
			if (refreshViewer && !fTreeViewer.getControl().isDisposed()) {
				fTreeViewer.refresh(element);
			}
		} else {
			if (!hasMatches(element)) {
				fChildrenMap.remove(element);
				Object parent= getParent(element);
				if (parent != null) {
					removeFromSiblings(element, parent);
					remove(parent, refreshViewer);
				} else {
					removeFromSiblings(element, fResult);
					if (refreshViewer && !fTreeViewer.getControl().isDisposed()) {
						fTreeViewer.refresh();
					}
				}
			} else {
				if (refreshViewer && !fTreeViewer.getControl().isDisposed()) {
					fTreeViewer.refresh(element);
				}
			}
		}
	}

	private boolean hasMatches(Object element) {
		/*
		if (element instanceof LineElement) {
			LineElement lineElement= (LineElement) element;
			return lineElement.getNumberOfMatches(fResult) > 0;
		}
		 */
		return fResult.getMatchCount(element) > 0;
	}

	private void removeFromSiblings(Object element, Object parent) {
		Set<Object> siblings= fChildrenMap.get(parent);
		if (siblings != null) {
			siblings.remove(element);
		}
	}

	private boolean insertChild(Object parent, Object child) {
		Set<Object> children = fChildrenMap.get(parent);
		if (children == null) {
			children= new HashSet<Object>();
			fChildrenMap.put(parent, children);
		}
		return children.add(child);
	}


	public Object[] getElements(Object inputElement) {
		Object[] children= getChildren(inputElement);
		
		System.out.println("getElements: " + children.length);

		return children;
	}

	public Object[] getChildren(Object parentElement) {
		Set<Object> children = fChildrenMap.get(parentElement);
		if (children == null) {
			return EMPTY;
		} else {
			return children.toArray();
		}
	}

	/**
	 * Return the parent of 
	 */
	public Object getParent(Object element) {
		if (element instanceof IProject) {
			return null;
		}
		if (element instanceof IResource) {
			IResource resource = (IResource) element;
			return resource.getParent();
		}
		
		return null;
	}

	public boolean hasChildren(Object element) {
		return getChildren(element).length > 0;
	}
	
	public synchronized void elementsChanged(Object[] updatedElements) {
		for (int i= 0; i < updatedElements.length; i++) {
//			if (!(updatedElements[i] instanceof LineElement)) {
				// change events to elements are reported in file search
				if (fResult.getMatchCount(updatedElements[i]) > 0)
					insert(updatedElements[i], true);
				else 
					remove(updatedElements[i], true);
/*				
			} else {
				// change events to line elements are reported in text search
				LineElement lineElement= (LineElement) updatedElements[i];
				int nMatches= lineElement.getNumberOfMatches(fResult);
				if (nMatches > 0) {
					if (hasChild(lineElement.getParent(), lineElement)) {
						fTreeViewer.update(new Object[] { lineElement, lineElement.getParent() }, null);
					} else {
						insert(lineElement, true);
					}
				} else {
					remove(lineElement, true);
				}
			}
 */
		}
	}
	
	public void clear() {
		initialize(fResult);
		if (!fTreeViewer.getControl().isDisposed()) {
			fTreeViewer.refresh();
		}
	}

}
