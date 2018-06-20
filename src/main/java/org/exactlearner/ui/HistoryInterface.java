package org.exactlearner.ui;

import java.awt.BorderLayout;
import java.awt.EventQueue;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Vector;

import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.SwingConstants;
import javax.swing.border.EmptyBorder;
import javax.swing.table.DefaultTableCellRenderer;
import javax.swing.table.DefaultTableModel;
import javax.swing.table.TableColumnModel;

public class HistoryInterface extends JFrame {

	private JPanel contentPane;

	/**
	 * Launch the application.
	 */
	public static void main(String[] args) {
		EventQueue.invokeLater(new Runnable() {
			public void run() {
				try {

					Object[] historyStuff = {1, "okgo - okgnotgo", "yes"};
					Vector<Object[]> historyD = new Vector<Object[]>();
					historyD.addElement(historyStuff);
					historyD.addElement(historyStuff);
					historyD.addElement(historyStuff);
					historyD.addElement(historyStuff);
					historyD.addElement(historyStuff);
					historyD.addElement(historyStuff);
					historyD.addElement(historyStuff);
					historyD.addElement(historyStuff);
					historyD.addElement(historyStuff);
					historyD.addElement(historyStuff);
					historyD.addElement(historyStuff);
					historyD.addElement(historyStuff);
					HistoryInterface frame = new HistoryInterface(historyD);
					frame.setVisible(true);
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
		});
	}

	/**
	 * Create the frame.
	 */
  
	public JPanel fieldPanel = new JPanel(new BorderLayout(0, 40));
	public JPanel historyPanel = new JPanel(new BorderLayout(0, 40));
	 public JPanel historyField = new JPanel(new BorderLayout());
	public JLabel historyTitle = new JLabel("History Queries");
	public String[] columenNames = {"NO.", "Query", "Answer"};
	public JTable historyTable;
	public DefaultTableModel tableModel = new DefaultTableModel(columenNames, 0);
	
	public HistoryInterface(Vector<Object[]> historyData) {
		super();
		setTitle("ExactLearner - Entailment Query History");
		
		setTitle("Ontology Learning Tool - EL TBoxes: History");
		setSize(600,480);
		setLocation(100, 50);
		setResizable(false);
		setVisible(true);
		 
		
		historyPanel.add(historyTitle, BorderLayout.NORTH);
	
		int numOfRow = historyData.size();

		if (numOfRow > 0){
			for (int i = 0; i < numOfRow; i++){
				tableModel.addRow(historyData.get(i));
			}
		}
		
		historyTable = new JTable(tableModel); 
		historyTable.getTableHeader().setReorderingAllowed(false);
		TableColumnModel colmodel = historyTable.getColumnModel();
				
		colmodel.getColumn(0).setPreferredWidth(50);
		colmodel.getColumn(0).setResizable(false);
		colmodel.getColumn(1).setPreferredWidth(450);
		colmodel.getColumn(1).setResizable(true);
		colmodel.getColumn(2).setPreferredWidth(75);
		colmodel.getColumn(2).setResizable(false);
		DefaultTableCellRenderer render = new DefaultTableCellRenderer();
	    render.setHorizontalAlignment(SwingConstants.CENTER);
	    colmodel.getColumn(0).setCellRenderer(render);
		
		final JScrollPane scrollPane = new JScrollPane(historyTable);
		scrollPane.setVerticalScrollBarPolicy(JScrollPane.VERTICAL_SCROLLBAR_ALWAYS); 
		
		historyField.add(scrollPane, BorderLayout.CENTER);
		historyPanel.add(historyField, BorderLayout.CENTER);
		 
		fieldPanel.add(historyPanel, BorderLayout.CENTER);
		
		add(fieldPanel, BorderLayout.CENTER);
		JButton btn = new JButton("Back"); 
		btn.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent arg0) {
				dispose();

			}
		});
		add(btn, BorderLayout.SOUTH);
		
	}
}
