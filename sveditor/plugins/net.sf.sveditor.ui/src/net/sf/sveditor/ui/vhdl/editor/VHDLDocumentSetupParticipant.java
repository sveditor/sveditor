package net.sf.sveditor.ui.vhdl.editor;

import org.eclipse.core.filebuffers.IDocumentSetupParticipant;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentExtension3;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.rules.FastPartitioner;

public class VHDLDocumentSetupParticipant implements IDocumentSetupParticipant {

	public void setup(IDocument document) {
		if (document instanceof IDocumentExtension3) {
			IDocumentExtension3 docExt = (IDocumentExtension3)document;
			IDocumentPartitioner part = new FastPartitioner(
					new VHDLPartitionScanner(),
					VHDLDocumentPartitions.VHD_PARTITION_TYPES);
			docExt.setDocumentPartitioner(
					VHDLDocumentPartitions.VHD_PARTITIONING, part);
			part.connect(document);
		}
	}

}
