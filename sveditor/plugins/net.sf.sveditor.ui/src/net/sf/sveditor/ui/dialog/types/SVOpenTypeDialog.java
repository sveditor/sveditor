package net.sf.sveditor.ui.dialog.types;

import java.util.Comparator;
import java.util.List;

import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.search.SVDBAllTypeMatcher;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.jface.dialogs.IDialogSettings;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.dialogs.FilteredItemsSelectionDialog;

public class SVOpenTypeDialog extends FilteredItemsSelectionDialog {
	private ISVDBIndexIterator		fIndexIt;
	
	public SVOpenTypeDialog(ISVDBIndexIterator index_it, Shell shell) {
		super(shell, false);
		fIndexIt = index_it;
		
		setListLabelProvider(new SVTreeLabelProvider());
		setDetailsLabelProvider(new SVTreeLabelProvider());
	}

	@Override
	protected Control createExtendedContentArea(Composite parent) {
		// TODO Auto-generated method stub
		return null;
	}
	
	private static final String DIALOG_SETTINGS = "SVOpenTypeDialogSettings";

	@Override
	protected IDialogSettings getDialogSettings() {
		IDialogSettings settings = SVUiPlugin.getDefault().getDialogSettings().getSection(DIALOG_SETTINGS);
		
		if (settings == null) {
			settings = SVUiPlugin.getDefault().getDialogSettings().addNewSection(DIALOG_SETTINGS);
		}
		
		return settings;
	}

	@Override
	protected IStatus validateItem(Object item) {
		return Status.OK_STATUS;
	}

	@Override
	protected ItemsFilter createFilter() {
		return new ItemsFilter() {
			
			@Override
			public boolean matchItem(Object item) {
				if (item instanceof SVDBDeclCacheItem) {
					return matches(((SVDBDeclCacheItem)item).getName());
				} else {
					// Error, really
					return matches(item.toString());
				}
			}
			
			@Override
			public boolean isConsistentItem(Object item) {
				return true;
			}
		};
	}

	@Override
	@SuppressWarnings("rawtypes")
	protected Comparator getItemsComparator() {
		return new Comparator() {
			public int compare(Object o1, Object o2) {
				if (o1 instanceof SVDBDeclCacheItem && o2 instanceof SVDBDeclCacheItem) {
					SVDBDeclCacheItem i1 = (SVDBDeclCacheItem)o1;
					SVDBDeclCacheItem i2 = (SVDBDeclCacheItem)o2;
					return i1.getName().compareTo(i2.getName());
				} else {
					return 0;
				}
			}
		};
	}

	@Override
	protected void fillContentProvider(
			AbstractContentProvider 	content_provider,
			ItemsFilter 				filter, 
			IProgressMonitor 			monitor) throws CoreException {
		int count = 0;
		ISVDBIndexIterator index_it = fIndexIt;
		SubProgressMonitor find_monitor = new SubProgressMonitor(monitor, 1);
		List<SVDBDeclCacheItem> items = 
				index_it.findGlobalScopeDecl(find_monitor, "", new SVDBAllTypeMatcher());
		
		synchronized (items) {
			for (SVDBDeclCacheItem i : items) {
				content_provider.add(i, filter);
				count++;
			}
		}
		
		System.out.println("Added " + count + " items");
		
		monitor.done();
	}

	@Override
	public String getElementName(Object item) {
		if (item instanceof SVDBDeclCacheItem) {
			SVDBDeclCacheItem ci = (SVDBDeclCacheItem)item;
			return ci.getName();
		} else {
			return item.toString();
		}
	}
}
