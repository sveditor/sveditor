package net.sf.sveditor.core.vhdl.parser;

public class VHFactories {
	private EntityFactory		m_entity;

	public EntityFactory entity() {
		if (m_entity == null) {
			m_entity = new EntityFactory(this);
		}
		return m_entity;
	}
}
