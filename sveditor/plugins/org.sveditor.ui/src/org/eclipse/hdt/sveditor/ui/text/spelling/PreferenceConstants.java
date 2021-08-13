/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.eclipse.hdt.sveditor.ui.text.spelling;

public class PreferenceConstants {

	/**
	 * A named preference that controls whether Java comments should be
	 * spell checked.
	 * <p>
	 * Value is of type <code>Boolean</code>.
	 * </p>
	 *
	 * @deprecated since 3.1, use {@link org.eclipse.ui.texteditor.spelling.SpellingService#PREFERENCE_SPELLING_ENABLED}
	 *             and {@link org.eclipse.ui.texteditor.spelling.SpellingService#PREFERENCE_SPELLING_ENGINE}
	 * @since 3.0
	 */
	public final static String SPELLING_CHECK_SPELLING= "spelling_check_spelling"; //$NON-NLS-1$

	/**
	 * A named preference that controls whether words containing digits should
	 * be skipped during spell checking.
	 * <p>
	 * Value is of type <code>Boolean</code>.
	 * </p>
	 *
	 * @since 3.0
	 */
	public final static String SPELLING_IGNORE_DIGITS= "spelling_ignore_digits"; //$NON-NLS-1$

	/**
	 * A named preference that controls whether mixed case words should be
	 * skipped during spell checking.
	 * <p>
	 * Value is of type <code>Boolean</code>.
	 * </p>
	 *
	 * @since 3.0
	 */
	public final static String SPELLING_IGNORE_MIXED= "spelling_ignore_mixed"; //$NON-NLS-1$

	/**
	 * A named preference that controls whether sentence capitalization should
	 * be ignored during spell checking.
	 * <p>
	 * Value is of type <code>Boolean</code>.
	 * </p>
	 *
	 * @since 3.0
	 */
	public final static String SPELLING_IGNORE_SENTENCE= "spelling_ignore_sentence"; //$NON-NLS-1$

	/**
	 * A named preference that controls whether upper case words should be
	 * skipped during spell checking.
	 * <p>
	 * Value is of type <code>Boolean</code>.
	 * </p>
	 *
	 * @since 3.0
	 */
	public final static String SPELLING_IGNORE_UPPER= "spelling_ignore_upper"; //$NON-NLS-1$

	/**
	 * A named preference that controls whether URLs should be ignored during
	 * spell checking.
	 * <p>
	 * Value is of type <code>Boolean</code>.
	 * </p>
	 *
	 * @since 3.0
	 */
	public final static String SPELLING_IGNORE_URLS= "spelling_ignore_urls"; //$NON-NLS-1$

	/**
	 * A named preference that controls whether single letters
	 * should be ignored during spell checking.
	 * <p>
	 * Value is of type <code>Boolean</code>.
	 * </p>
	 *
	 * @since 3.3
	 */
	public final static String SPELLING_IGNORE_SINGLE_LETTERS= "spelling_ignore_single_letters"; //$NON-NLS-1$

	/**
	 * A named preference that controls whether '&' in
	 * Java properties files are ignored.
	 * <p>
	 * Value is of type <code>Boolean</code>.
	 * </p>
	 *
	 * @since 3.3
	 */
	public final static String SPELLING_IGNORE_AMPERSAND_IN_PROPERTIES= "spelling_ignore_ampersand_in_properties"; //$NON-NLS-1$

	/**
	 * A named preference that controls whether non-letters at word boundaries
	 * should be ignored during spell checking.
	 * <p>
	 * Value is of type <code>Boolean</code>.
	 * </p>
	 *
	 * @since 3.3
	 */
	public final static String SPELLING_IGNORE_NON_LETTERS= "spelling_ignore_non_letters"; //$NON-NLS-1$

	/**
	 * A named preference that controls whether Java strings
	 * should be ignored during spell checking.
	 * <p>
	 * Value is of type <code>Boolean</code>.
	 * </p>
	 *
	 * @since 3.4
	 */
	public static final String SPELLING_IGNORE_JAVA_STRINGS= "spelling_ignore_java_strings"; //$NON-NLS-1$;

	/**
	 * A named preference that controls the locale used for spell checking.
	 * <p>
	 * Value is of type <code>String</code>.
	 * </p>
	 *
	 * @since 3.0
	 */
	public final static String SPELLING_LOCALE= "spelling_locale"; //$NON-NLS-1$

	/**
	 * A named preference that controls the number of proposals offered during
	 * spell checking.
	 * <p>
	 * Value is of type <code>Integer</code>.
	 * </p>
	 *
	 * @since 3.0
	 */
	public final static String SPELLING_PROPOSAL_THRESHOLD= "spelling_proposal_threshold"; //$NON-NLS-1$

	/**
	 * A named preference that controls the maximum number of problems reported during spell checking.
	 * <p>
	 * Value is of type <code>Integer</code>.
	 * </p>
	 *
	 * @since 3.4
	 */
	public final static String SPELLING_PROBLEMS_THRESHOLD= "spelling_problems_threshold"; //$NON-NLS-1$

	/**
	 * A named preference that specifies the workspace user dictionary.
	 * <p>
	 * Value is of type <code>Integer</code>.
	 * </p>
	 *
	 * @since 3.0
	 */
	public final static String SPELLING_USER_DICTIONARY= "spelling_user_dictionary"; //$NON-NLS-1$

	/**
	 * A named preference that specifies encoding of the workspace user dictionary.
	 * <p>
	 * Value is of type <code>String</code>.
	 * </p>
	 *
	 * @since 3.3
	 */
	public final static String SPELLING_USER_DICTIONARY_ENCODING= "spelling_user_dictionary_encoding"; //$NON-NLS-1$

	/**
	 * A named preference that specifies whether spelling dictionaries are available to content assist.
	 *
	 * <strong>Note:</strong> This is currently not supported because the spelling engine
	 * cannot return word proposals but only correction proposals.
	 * <p>
	 * Value is of type <code>Boolean</code>.
	 * </p>
	 *
	 * @since 3.0
	 */
	public final static String SPELLING_ENABLE_CONTENTASSIST= "spelling_enable_contentassist"; //$NON-NLS-1$

}
