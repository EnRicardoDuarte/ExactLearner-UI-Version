package org.exactlearner.ui;

import java.awt.EventQueue;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;

import javax.swing.JButton;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JTextField;
import javax.swing.border.EmptyBorder;
import javax.swing.filechooser.FileNameExtensionFilter;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeEvent;

public class LoadFromFile extends JFrame {

	private JPanel contentPane;
	private JTextField filePath;

	/**
	 * Launch the application.
	 */
	public static void main(String[] args) {
		EventQueue.invokeLater(new Runnable() {
			public void run() {
				try {
					LoadFromFile frame = new LoadFromFile();
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
	public LoadFromFile() {
		setTitle("ExactLearner - Load from file");
		setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		setBounds(100, 100, 450, 173);
		contentPane = new JPanel();
		contentPane.setBorder(new EmptyBorder(5, 5, 5, 5));
		setContentPane(contentPane);
		contentPane.setLayout(null);
		
		JLabel lblNewLabel = new JLabel("Select the ontology to load from your disk:");
		lblNewLabel.setBounds(10, 11, 414, 14);
		contentPane.add(lblNewLabel);
		
		JButton backButton = new JButton("Back");
		backButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				(new StartUILearner()).setVisible(true);
				dispose();
			}
		});
		backButton.setBounds(10, 102, 89, 23);
		contentPane.add(backButton);
		
		JButton loadButton = new JButton("Load");
		loadButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				
				(new ExLeInterface(new File(filePath.getText()))).setVisible(true);
				dispose();
			}
		});
		loadButton.setEnabled(false);
		loadButton.setBounds(335, 102, 89, 23);
		contentPane.add(loadButton);
		
		filePath = new JTextField();
		filePath.addPropertyChangeListener(new PropertyChangeListener() {
			public void propertyChange(PropertyChangeEvent arg0) { 
				loadButton.setEnabled(true);
			}
		});
		filePath.setEditable(false);
		filePath.setBounds(10, 38, 200, 20);
		contentPane.add(filePath);
		filePath.setColumns(10);
		
		JButton btnNewButton = new JButton("Browse");
		btnNewButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				JFileChooser fc = new JFileChooser(new File("/src/main/resources/ontologies"));

				fc.setDialogTitle("Open class File");
				fc.setApproveButtonText("Open");
				fc.setAcceptAllFileFilterUsed(false);
				fc.addChoosableFileFilter(new FileNameExtensionFilter("Ontology File (*.owl)", "owl"));
				int returnVal = fc.showOpenDialog(fc);

				File file = null;
				if (returnVal == JFileChooser.APPROVE_OPTION) {
					file = fc.getSelectedFile();
					// System.out.println(file.getPath());
					filePath.setText(file.getPath());

				}
			}
		});
		btnNewButton.setBounds(221, 36, 89, 23);
		contentPane.add(btnNewButton);
	}
}
