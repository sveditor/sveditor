package net.sf.sveditor.ui.editor;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.parser.SVKeywords;

import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.rules.ICharacterScanner;
import org.eclipse.jface.text.rules.IPartitionTokenScanner;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.ITokenScanner;
import org.eclipse.jface.text.rules.IWordDetector;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.rules.WordRule;

public class SVScanners {
	
	private static SVScanners			fDefault;
	
	private ITokenScanner				fPresentationScanner;
	private IPartitionTokenScanner		fPartitionScanner;

	private SVScanners() {
		
	}
	
	private static SVScanners getDefault() {
		if (fDefault == null) {
			fDefault = new SVScanners();
		}
		
		return fDefault;
	}
	
	private ITokenScanner newPresentationScanner() {
		IToken keyword = new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.KEYWORD),
				null, SVEditorColors.getStyle(SVEditorColors.KEYWORD)));
		final IToken str = new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.STRING),
				null, SVEditorColors.getStyle(SVEditorColors.STRING)));
		
		IToken default_t = new Token(new TextAttribute(
				SVEditorColors.getColor(SVEditorColors.DEFAULT),
				null, SVEditorColors.getStyle(SVEditorColors.DEFAULT)));
		
		List<IRule> rules = new ArrayList<IRule>();

		rules.add(new IRule() {
			public IToken evaluate(ICharacterScanner scanner) {
				int startCh = scanner.read();
				int ch;
				int unreadCount = 1;
				
				if (startCh == '"') {
					do {
						ch = scanner.read();
					} while (Character.isDefined((char)ch) && ch != '"');
					
					return str;
				}
				
				do {
					scanner.unread();
				} while (--unreadCount > 0);
				return Token.UNDEFINED;
			}
		});

		WordRule wordRule = new WordRule(new IWordDetector() {
			public boolean isWordPart(char c) {
				return Character.isJavaIdentifierPart(c);
			}
			
			public boolean isWordStart(char c) {
				return Character.isJavaIdentifierStart(c);
			}
		}, default_t);
		
		for (String kw :SVKeywords.getKeywords()) {
			String kw_p = kw;
			if (kw.endsWith("*")) {
				kw_p = kw.substring(0, kw.length()-1);
			}
			wordRule.addWord(kw_p, keyword);
		}
		
		rules.add(wordRule);
		
		IRule[] ruleArray = rules.toArray(new IRule[rules.size()]);
		RuleBasedScanner ret = new RuleBasedScanner();
		ret.setRules(ruleArray);
		
		return ret;
	}
	
	public static ITokenScanner getPresentationScanner() {
		ITokenScanner ret = getDefault().fPresentationScanner;
		
		if (ret == null) {
			ret = getDefault().newPresentationScanner();
			getDefault().fPresentationScanner = ret;
		}
		
		return ret;
	}
	
	public static IPartitionTokenScanner getPartitionScanner() {
		IPartitionTokenScanner ret = getDefault().fPartitionScanner;
		
		if (ret == null) {
			ret = new SVPartitionScanner();
			getDefault().fPartitionScanner = ret;
		}
		
		return ret;
	}
	
}
